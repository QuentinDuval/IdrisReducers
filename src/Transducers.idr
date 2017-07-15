module Transducers


--------------------------------------------------------------------------------
-- Core (definition of a step)
--------------------------------------------------------------------------------

export
data Status a = Done a | Continue a

export
unStatus : Status a -> a
unStatus (Done a) = a
unStatus (Continue a) = a

export
implementation Functor Status where
  map f (Done a) = Done (f a)
  map f (Continue a) = Continue (f a)

export
StatelessStep : (acc: Type) -> (elem: Type) -> Type
StatelessStep acc elem = acc -> elem -> acc

export
Step : (state: Type) -> (acc: Type) -> (elem: Type) -> Type
Step state acc elem = state -> acc -> elem -> Status (state, acc)

public export
record Reducer st acc elem where
  constructor MkReducer
  state : st
  runStep : Step st acc elem
  complete : st -> acc -> acc

public export
Transducer : (acc: Type) -> (s1, s2: Type) -> (inner, outer: Type) -> Type
Transducer acc s1 s2 inner outer = Reducer s1 acc inner -> Reducer s2 acc outer


-------------------------------------------------------------------------------
-- Helpers to build stateless Reducers and Transducers
--------------------------------------------------------------------------------

namespace StatelessStep

  export
  stateless : StatelessStep acc elem -> Reducer () acc elem
  stateless fn = MkReducer () step (const id)
    where step = \_, acc, elem => Continue ((), fn acc elem)

namespace StatelessTransducer

  export
  stateless : (Step s acc inner -> Step s acc outer) -> Transducer acc s s inner outer
  stateless onStep xf = MkReducer (state xf) (onStep (runStep xf)) (complete xf)

export
noComplete : s' -> (Step s acc inner -> Step (s', s) acc outer) -> Transducer acc s (s', s) inner outer
noComplete initState onStep xf = MkReducer
  (initState, state xf)
  (onStep (runStep xf))
  (\state => complete xf (snd state))


--------------------------------------------------------------------------------
-- Core (Reductions)
--------------------------------------------------------------------------------

export
withState : s' -> Status (s, acc) -> Status ((s', s), acc)
withState s' = map (\(s, acc) => ((s', s), acc))

export
runSteps : (Foldable t) => Step st acc elem -> (st, acc) -> t elem -> Status (st, acc)
runSteps step start elems = foldr compStep id elems (Continue start)
  where
    compStep elem f result =
      case result of
        Done done => Done done
        Continue (st, acc) => f (step st acc elem)

export
reduce : (Foldable t) => Reducer st acc elem -> acc -> t elem -> acc
reduce step result =
  uncurry (complete step)
    . unStatus
    . runSteps (runStep step) (state step, result)

export
transduce : (Foldable t) => Transducer acc () s a b -> (acc -> a -> acc) -> acc -> t b -> acc
transduce xf step = reduce (xf (stateless step))


--------------------------------------------------------------------------------
-- Core (syntaxic sugar to compose Transducers)
--------------------------------------------------------------------------------

infixr 5 |>

(|>) : (b -> c) -> (a -> b) -> (a -> c)
(|>) r2 r1 = r2 . r1


--------------------------------------------------------------------------------
-- Basic Transducers (stateless)
--------------------------------------------------------------------------------

export
mapping : (outer -> inner) -> Transducer acc s s inner outer
mapping fn = stateless $
  \next, st, acc, outer => next st acc (fn outer)

export
filtering : (elem -> Bool) -> Transducer acc s s elem elem
filtering pf = stateless $
  \next, st, acc, elem =>
    if pf elem then next st acc elem else Continue (st, acc)

export
catMapping : (Foldable t) => (outer -> t inner) -> Transducer acc s s inner outer
catMapping fn = stateless $
  \next, st, acc, outer => runSteps next (st, acc) (fn outer)


--------------------------------------------------------------------------------
-- Basic Transducers (stateful)
--------------------------------------------------------------------------------

export
dropping : Nat -> Transducer acc s (Nat, s) elem elem
dropping n = noComplete n dropImpl
  where
    dropImpl next (S n, st) acc elem = Continue ((n, st), acc)
    dropImpl next (Z, st) acc elem =
      withState Z (next st acc elem)

export
taking : Nat -> Transducer acc s (Nat, s) elem elem
taking n = noComplete n takeImpl
  where
    takeImpl next (Z, st) acc elem = Done ((Z, st), acc)
    takeImpl next (n, st) acc elem =
      withState (pred n) (next st acc elem)

export
interspersing : elem -> Transducer acc s (Bool, s) elem elem
interspersing separator = noComplete False stepImpl
  where
    stepImpl next (False, st) acc e =
      withState True (next st acc e)
    stepImpl next (True, st) acc e =
      withState True (runSteps next (st, acc) [separator, e])

export
chunksOf : Nat -> Transducer acc s (List elem, s) (List elem) elem
chunksOf chunkSize xf = MkReducer ([], state xf) nextChunk dumpRemaining
  where
    nextChunk (remaining, st) acc elem =
      let remaining' = elem :: remaining in
      if length remaining' == chunkSize
        then withState [] $ runStep xf st acc (reverse remaining')
        else Continue ((remaining', st), acc)
    dumpRemaining (remaining, st) acc =
      let (st', acc') =
            if length remaining == 0
              then (st, acc)
              else unStatus (runStep xf st acc (reverse remaining))
      in complete xf st' acc'


--------------------------------------------------------------------------------
-- Unit tests
--------------------------------------------------------------------------------

assertThat : Bool -> String -> IO ()
assertThat test errorMsg = if test
  then putStrLn "Test Passed"
  else putStrLn $ "Test Failed: " ++ errorMsg

assertEq : (Eq a, Show a) => (expected : a) -> (given : a) -> IO ()
assertEq e g =
  assertThat (g == e) $
    "Expected == " ++ show e ++ ", Got: " ++ show g

odd : Int -> Bool
odd n = mod n 2 == 1

twice : Int -> List Int
twice = replicate 2

should_map : List Int -> IO ()
should_map input =
  assertEq
    (foldl (+) 0 (map (*2) input))
    (transduce (mapping (*2)) (+) 0 input)

should_filter : List Int -> IO ()
should_filter input =
  assertEq
    (foldl (+) 0 (filter odd input))
    (transduce (filtering odd) (+) 0 input)

should_concat_map : List Int -> IO ()
should_concat_map input =
  assertEq
    (foldl (+) 0 (concatMap twice input))
    (transduce (catMapping twice) (+) 0 input)

should_take : List Int -> IO ()
should_take input =
  assertEq
    (foldl (+) 0 (take 10 input))
    (transduce (taking 10) (+) 0 input)

should_drop : List Int -> IO ()
should_drop input =
  assertEq
    (foldl (+) 0 (drop 10 input))
    (transduce (dropping 10) (+) 0 input)

should_pipe_from_left_to_right : List Int -> IO ()
should_pipe_from_left_to_right input =
  assertEq
    (foldl (+) 0 (map (+1) (concatMap twice (filter odd input))))
    (transduce (filtering odd |> catMapping twice |> mapping (+1)) (+) 0 input)

should_allow_pure_xf_composition : IO ()
should_allow_pure_xf_composition =
  let xf = taking 10 . filtering odd . mapping (*2)
  in do
    assertEq 50 (transduce xf (+) 0 [1..100])
    assertEq 30240 (transduce xf (*) 1 [1..100])

should_chunk_of : IO ()
should_chunk_of = do
  let xf = chunksOf 4 . mapping pack . mapping (++ " ")
  assertEq "abcd efgh ijkl " (transduce xf (++) "" ['a'..'l'])
  assertEq "abcd efgh ij " (transduce xf (++) "" ['a'..'j'])

should_intersperse : IO ()
should_intersperse = do
  let cs = ["a", "list", "of", "words"]
  assertEq "a, list, of, words" (transduce (interspersing ", ") (++) "" cs)

export
run_tests : IO ()
run_tests = do
  should_map [1..100]
  should_filter [1..100]
  should_concat_map [1..100]
  should_take [1..100]
  should_drop [1..100]
  should_pipe_from_left_to_right [1..100]
  should_allow_pure_xf_composition
  should_chunk_of
  should_intersperse

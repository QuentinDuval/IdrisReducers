module Transducers


--------------------------------------------------------------------------------
-- Core (definition of a step)
--------------------------------------------------------------------------------

export
data Status a = Done a | Continue a

export
StatelessStep : (acc: Type) -> (elem: Type) -> Type
StatelessStep acc elem = acc -> elem -> acc

export
Step : (state: Type) -> (acc: Type) -> (elem: Type) -> Type
Step state acc elem = state -> acc -> elem -> (state, Status acc)

public export
record Reducer st acc elem where
  constructor MkReducer
  state : st
  next : Step st acc elem
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
    where step = \_, acc, elem => ((), Continue (fn acc elem))

namespace StatelessTransducer

  export
  stateless : (Reducer s acc inner -> Step s acc outer) -> Transducer acc s s inner outer
  stateless transducer xf = MkReducer (state xf) (transducer xf) (complete xf)


--------------------------------------------------------------------------------
-- Core (Reductions)
--------------------------------------------------------------------------------

unStatus : (st, Status a) -> (st, a)
unStatus (st, Done a) = (st, a)
unStatus (st, Continue a) = (st, a)

runSteps : (Foldable t) => Step st acc elem -> (st, acc) -> t elem -> (st, Status acc)
runSteps step (st, acc) elems = foldr compStep id elems (st, Continue acc)
  where
    compStep elem f result@(st, status) =
      case status of
        Done acc => result
        Continue acc => f (step st acc elem)

export
reduce : (Foldable t) => Reducer st acc elem -> acc -> t elem -> acc
reduce step result =
  uncurry (complete step)
    . unStatus
    . runSteps (next step) (state step, result)

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
  \xf, st, acc, outer => next xf st acc (fn outer)

export
filtering : (elem -> Bool) -> Transducer acc s s elem elem
filtering pf = stateless $
  \xf, st, acc, elem =>
    if pf elem then next xf st acc elem else (st, Continue acc)

export
catMapping : (Foldable t) => (outer -> t inner) -> Transducer acc s s inner outer
catMapping fn = stateless $
  \xf, st, acc, outer => runSteps (next xf) (st, acc) (fn outer)


--------------------------------------------------------------------------------
-- Basic Transducers (stateful)
--------------------------------------------------------------------------------

dropping : Nat -> Transducer acc s (Nat, s) elem elem
dropping n xf = MkReducer (n, state xf) dropImpl (\(n, st), elem => complete xf st elem)
  where
    dropImpl (S n, st) acc elem = ((n, st), Continue acc)
    dropImpl (Z, st) acc elem =
      let (st', acc') = next xf st acc elem
      in ((Z, st'), acc')

taking : Nat -> Transducer acc s (Nat, s) elem elem
taking n xf = MkReducer (n, state xf) takeImpl (\(n, st), elem => complete xf st elem)
  where
    takeImpl (Z, st) acc elem = ((0, st), Done acc)
    takeImpl (n, st) acc elem =
      let (st', acc') = next xf st acc elem
      in ((pred n, st'), acc')

-- TODO: use take?

export
chunksOf : Nat -> Transducer acc s (List elem, s) (List elem) elem
chunksOf chunkSize xf = MkReducer ([], state xf) nextChunk dumpRemaining
  where
    nextChunk (remaining, st) acc elem =
      let remaining' = elem :: remaining in
      if length remaining' == chunkSize
        then let (st, acc) = next xf st acc (reverse remaining')
             in (([], st), acc)
        else ((remaining', st), Continue acc)
    dumpRemaining (remaining, st) acc =
      let (st', acc') =
            if length remaining == 0
              then (st, acc)
              else unStatus (next xf st acc (reverse remaining))
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

--should_work_with_foldr : List Int -> IO ()
--should_work_with_foldr input =
  --assertEq
    --(foldr (::) [] (map (+1) (filter odd input)))
    --(foldr (flip (filtering odd |> mapping (+1) |> flip (::))) [] input)

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


export
run_tests : IO ()
run_tests = do
  should_map [1..100]
  should_filter [1..100]
  should_concat_map [1..100]
  should_take [1..100]
  should_drop [1..100]
  should_pipe_from_left_to_right [1..100]
  -- should_work_with_foldr [1..100]
  should_allow_pure_xf_composition
  should_chunk_of

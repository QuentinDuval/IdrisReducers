module Reducers


--------------------------------------------------------------------------------
-- Core (definition of a step)
--------------------------------------------------------------------------------

public export
record Step st acc elem where
  constructor MkStep
  state : st
  next : st -> acc -> elem -> (st, acc)
  complete : st -> acc -> acc

public export
Reducer : (acc: Type) -> (s1: Type) -> (s2: Type) -> (a: Type) -> (b: Type) -> Type
Reducer acc s1 s2 a b = Step s1 acc a -> Step s2 acc b


-------------------------------------------------------------------------------
-- Helpers to build stateless steps and reducers
--------------------------------------------------------------------------------

namespace StatelessStep

  export
  stateless : (acc -> elem -> acc) -> Step () acc elem
  stateless fn = MkStep () (\_, acc, elem => ((), fn acc elem)) (const id)

namespace StatelessReducer

  export
  stateless : (Step s acc inner -> s -> acc -> outer -> (s, acc)) -> Reducer acc s s inner outer
  stateless xf step = MkStep (state step) (xf step) (complete step)


--------------------------------------------------------------------------------
-- Core (Reductions)
--------------------------------------------------------------------------------

reduceImpl : (Foldable t) => Step st acc elem -> (st, acc) -> t elem -> (st, acc)
reduceImpl step = foldl (\(st, acc) => next step st acc)

export
reduce : (Foldable t) => Step st acc elem -> acc -> t elem -> acc
reduce step result = uncurry (complete step) . reduceImpl step (state step, result)

export
transduce : (Foldable t) => Reducer acc () s a b -> (acc -> a -> acc) -> acc -> t b -> acc
transduce xf step = reduce (xf (stateless step))


--------------------------------------------------------------------------------
-- Core (syntaxic sugar to compose reducers)
--------------------------------------------------------------------------------

infixr 5 |>

(|>) : (b -> c) -> (a -> b) -> (a -> c)
(|>) r2 r1 = r2 . r1


--------------------------------------------------------------------------------
-- Basic reducers (stateless)
--------------------------------------------------------------------------------

export
mapping : (outer -> inner) -> Reducer acc s s inner outer
mapping fn = stateless $
  \step, st, acc, outer => next step st acc (fn outer)

export
filtering : (elem -> Bool) -> Reducer acc s s elem elem
filtering pf = stateless $
  \step, st, acc, elem => if pf elem then next step st acc elem else (st, acc)

export
catMapping : (Foldable t) => (outer -> t inner) -> Reducer acc s s inner outer
catMapping fn = stateless $
  \step, st, acc, outer => reduceImpl step (st, acc) (fn outer)


--------------------------------------------------------------------------------
-- Basic reducers (stateless)
--------------------------------------------------------------------------------

-- TODO: use take?

export
chunksOf : Nat -> Reducer acc s (List elem, s) (List elem) elem
chunksOf chunkSize step = MkStep ([], state step) nextChunk dumpRemaining
  where
    nextChunk (remaining, st) acc elem =
      let remaining' = elem :: remaining in
      if length remaining' == chunkSize
        then let (st, acc) = next step st acc (reverse remaining')
             in (([], st), acc)
        else ((remaining', st), acc)
    dumpRemaining (remaining, st) acc =
      let (st', acc') =
            if length remaining == 0
              then (st, acc)
              else next step st acc (reverse remaining)
      in complete step st' acc'


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

should_pipe_from_left_to_right : List Int -> IO ()
should_pipe_from_left_to_right input =
  assertEq
    (foldl (+) 0 (map (+1) (concatMap twice (filter odd input))))
    (transduce (filtering odd |> catMapping twice |> mapping (+1)) (+) 0 input)

{-
should_work_with_foldr : List Int -> IO ()
should_work_with_foldr input =
  assertEq
    (foldr (::) [] (map (+1) (filter odd input)))
    (foldr (flip (filtering odd |> mapping (+1) |> flip (::))) [] input)
-}

should_allow_pure_xf_composition : IO ()
should_allow_pure_xf_composition =
  let xf = filtering odd . mapping (*2)
  in do
    assertEq 50 (transduce xf (+) 0 [1..10])
    assertEq 30240 (transduce xf (*) 1 [1..10])

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
  should_pipe_from_left_to_right [1..100]
  -- should_work_with_foldr [1..100]
  should_allow_pure_xf_composition
  should_chunk_of

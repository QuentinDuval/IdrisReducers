module Reducers

%access export


--------------------------------------------------------------------------------
-- Core library
--------------------------------------------------------------------------------

record Step st acc elem where
  constructor MkStep
  state : st
  next : st -> acc -> elem -> (st, acc)
  complete : st -> acc -> acc

Reducer : (acc: Type) -> (s1: Type) -> (s2: Type) -> (a: Type) -> (b: Type) -> Type
Reducer acc s1 s2 a b = Step s1 acc a -> Step s2 acc b

-- StatelessReducer : (acc: Type) -> (a: Type) -> (b: Type) -> Type
-- StatelessReducer acc a b = forall s. Reducer acc s s a b

reduceImpl : (Foldable t) => Step st acc elem -> (st, acc) -> t elem -> (st, acc)
reduceImpl step = foldl (\(st, acc) => next step st acc)

reduce : (Foldable t) => Step st acc elem -> acc -> t elem -> acc
reduce step result = uncurry (complete step) . reduceImpl step (state step, result)

stateless : (acc -> elem -> acc) -> Step () acc elem
stateless fn = MkStep () (\_, acc, elem => ((), fn acc elem)) (const id)

transduce : (Foldable t) => Reducer acc () s a b -> (acc -> a -> acc) -> acc -> t b -> acc
transduce xf step = reduce (xf (stateless step))


--------------------------------------------------------------------------------
-- Composition of steps (helpers)
--------------------------------------------------------------------------------

infixr 5 |>

namespace TransducerComp
  (|>) : (b -> c) -> (a -> b) -> (a -> c)
  (|>) r2 r1 = r2 . r1


--------------------------------------------------------------------------------
-- Useful reducers
--------------------------------------------------------------------------------

mapping : (outer -> inner) -> Reducer acc s s inner outer
mapping fn step = MkStep
  (state step)
  (\st, acc, outer => next step st acc (fn outer))
  (complete step)


filtering : (elem -> Bool) -> Reducer acc s s elem elem
filtering pf step = MkStep
  (state step)
  (\st, acc, elem => if pf elem then next step st acc elem else (st, acc))
  (complete step)

catMapping : (Foldable t) => (outer -> t inner) -> Reducer acc s s inner outer
catMapping fn step = MkStep
  (state step)
  (\st, acc, outer => let inners = fn outer in reduceImpl step (st, acc) inners)
  (complete step)


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

run_tests : IO ()
run_tests = do
  should_map [1..100]
  should_filter [1..100]
  should_concat_map [1..100]
  should_pipe_from_left_to_right [1..100]
  -- should_work_with_foldr [1..100]
  should_allow_pure_xf_composition

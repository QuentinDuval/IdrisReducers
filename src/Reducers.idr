module Reducers

%access export

--------------------------------------------------------------------------------
-- Core library
--------------------------------------------------------------------------------

StepL : (acc: Type) -> (elem: Type) -> Type
StepL acc elem = acc -> elem -> acc

ReducerL : (acc: Type) -> (a: Type) -> (b: Type) -> Type
ReducerL acc a b = StepL acc a -> StepL acc b

infixr 5 |>

-- Automatically used inside a foldl / foldr, with the terminal element
namespace Reducer
  (|>) : ReducerL acc inner outer -> StepL acc inner -> StepL acc outer
  (|>) r step = r step

-- Only used when piping transformation without terminal element
namespace Transducer
  (|>) : ReducerL acc b c -> ReducerL acc a b -> ReducerL acc a c
  (|>) r2 r1 = r2 . r1


--------------------------------------------------------------------------------
-- Useful reducers
--------------------------------------------------------------------------------

mapping : (outer -> inner) -> ReducerL acc inner outer
mapping fn step = \acc, outer => step acc (fn outer)

filtering : (elem -> Bool) -> ReducerL acc elem elem
filtering pf step = \acc, elem => if pf elem then step acc elem else acc

catMapping : (Foldable t) => (outer -> t inner) -> ReducerL acc inner outer
catMapping fn step = \acc, outer => let inners = fn outer in foldl step acc inners


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
    (foldl (mapping (*2) (+)) 0 input)

should_filter : List Int -> IO ()
should_filter input =
  assertEq
    (foldl (+) 0 (filter odd input))
    (foldl (filtering odd (+)) 0 input)

should_concat_map : List Int -> IO ()
should_concat_map input =
  assertEq
    (foldl (+) 0 (concatMap twice input))
    (foldl (catMapping twice (+)) 0 input)

should_pipe_from_left_to_right : List Int -> IO ()
should_pipe_from_left_to_right input =
  let expected = foldl (+) 0 (map (+1) (concatMap twice (filter odd input)))
  in do
    assertEq expected $
      foldl (filtering odd |> catMapping twice |> mapping (+1) |> (+)) 0 input
    assertEq expected $
      foldl (filtering odd |> catMapping twice |> mapping (+1) (+)) 0 input

should_work_with_foldr : List Int -> IO ()
should_work_with_foldr input =
  assertEq
    (foldr (::) [] (map (+1) (filter odd input)))
    (foldr (flip (filtering odd |> mapping (+1) |> flip (::))) [] input)

should_allow_pure_xf_composition : IO ()
should_allow_pure_xf_composition =
  let xf = filtering odd |> mapping (*2)
  in do
    assertEq 50 (foldl (xf (+)) 0 [1..10])
    assertEq 30240 (foldl (xf (*)) 1 [1..10])

run_tests : IO ()
run_tests = do
  should_map [1..100]
  should_filter [1..100]
  should_concat_map [1..100]
  should_pipe_from_left_to_right [1..100]
  should_work_with_foldr [1..100]
  should_allow_pure_xf_composition

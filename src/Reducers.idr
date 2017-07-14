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

namespace Reducer
  (|>) : ReducerL acc b c -> ReducerL acc a b -> ReducerL acc a c
  (|>) r2 r1 = r2 . r1

namespace Terminal
  (|>) : ReducerL acc inner outer -> StepL acc inner -> StepL acc outer
  (|>) r step = r step


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
-- Some tests
--------------------------------------------------------------------------------

assertThat : Bool -> String -> IO ()
assertThat test errorMsg = if test
  then putStrLn "Test Passed"
  else putStrLn $ "Test Failed: " ++ errorMsg

assertEq : (Eq a, Show a) => (expected : a) -> (given : a) -> IO ()
assertEq e g =
  assertThat (g == e) $
    "Expected == " ++ show e ++ ", Got: " ++ show g

mapping_should_do_as_map : List Int -> IO ()
mapping_should_do_as_map input =
  assertEq
    (foldl (+) 0 (map (*2) input))
    (foldl (mapping (*2) (+)) 0 input)

filtering_should_do_as_filter : List Int -> IO ()
filtering_should_do_as_filter input =
  assertEq
    (foldl (+) 0 (filter odd input))
    (foldl (filtering odd (+)) 0 input)
  where
    odd n = mod n 2 == 0

catmapping_should_do_as_concatMap : List Int -> IO ()
catmapping_should_do_as_concatMap input =
  assertEq
    (foldl (+) 0 (concatMap twice input))
    (foldl (catMapping twice (+)) 0 input)
  where
    twice : Int -> List Int
    twice = replicate 2

run_tests : IO ()
run_tests = do
  mapping_should_do_as_map [1..10]
  filtering_should_do_as_filter [1..10]
  catmapping_should_do_as_concatMap [1..10]

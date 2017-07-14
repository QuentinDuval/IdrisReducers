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
odd n = mod n 2 == 0

twice : Int -> List Int
twice = replicate 2

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

catmapping_should_do_as_concatMap : List Int -> IO ()
catmapping_should_do_as_concatMap input =
  assertEq
    (foldl (+) 0 (concatMap twice input))
    (foldl (catMapping twice (+)) 0 input)

reducers_composition_is_reversed : List Int -> IO ()
reducers_composition_is_reversed input =
  let expected = foldl (+) 0 (map (+1) (concatMap twice (filter odd input)))
  in do
    assertEq expected $
      foldl (filtering odd |> catMapping twice |> mapping (+1) |> (+)) 0 input
    assertEq expected $
      foldl (filtering odd |> catMapping twice |> mapping (+1) (+)) 0 input

reducers_should_work_with_foldr : List Int -> IO ()
reducers_should_work_with_foldr input =
  assertEq
    (foldr (::) [] (map (+1) (filter odd input)))
    (foldr (flip (filtering odd |> mapping (+1) |> flip (::))) [] input)

run_tests : IO ()
run_tests = do
  mapping_should_do_as_map [1..100]
  filtering_should_do_as_filter [1..100]
  catmapping_should_do_as_concatMap [1..100]
  reducers_composition_is_reversed [1..100]
  reducers_should_work_with_foldr [1..100]

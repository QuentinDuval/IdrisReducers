module Test.Transducers.Examples

import Transducers
import Test.Transducers.Utils


--------------------------------------------------------------------------------

sumSquaresOfOdds : List Int -> Int
sumSquaresOfOdds = transduce (filtering odd . mapping (\x => x * x)) (+) 0

test_sumSquaresOfOdds : IO ()
test_sumSquaresOfOdds =
  assertEq (1 + 9 + 25 + 49 + 81) $ sumSquaresOfOdds [1..10]

--------------------------------------------------------------------------------

unwordSmallNames : Nat -> List String -> String
unwordSmallNames maxLength strings =
  transduce (filtering smallStrings . interspersing " ") (++) "" strings
  where smallStrings s = length s <= maxLength

test_unwordSmallNames : IO ()
test_unwordSmallNames =
  assertEq "a bbbb ddd e" $ unwordSmallNames 4 (words "a bbbb ccccc ddd e")

--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

export
run_tests : IO ()
run_tests = do
  test_sumSquaresOfOdds
  test_unwordSmallNames

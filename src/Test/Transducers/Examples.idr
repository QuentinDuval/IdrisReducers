module Test.Transducers.Examples

import Control.Monad.State
import Transducers
import Test.Transducers.Utils


--------------------------------------------------------------------------------

sumLength : StatelessStep Int String
sumLength totalLength str = totalLength + fromNat (length str)

test_sumLength : Test
test_sumLength =
  assertEq 10 (foldl sumLength 0 ["abc", "de", "", "fghij"])

--------------------------------------------------------------------------------

sumLengthOfEveryOddStrings : Step Bool Int String
sumLengthOfEveryOddStrings totalLength str = do
  doSum <- get
  modify not
  pure $ if doSum
    then Continue (sumLength totalLength str)
    else Continue (totalLength)

test_sumLengthOfEveryOddStrings : Test
test_sumLengthOfEveryOddStrings = do
  assertEq 6 $
    reduce (MkReducer True sumLengthOfEveryOddStrings (const id)) 0 ["abc", "de", "", "fg", "hij"]

--------------------------------------------------------------------------------

sumLengthUntil : Int -> Step () Int String
sumLengthUntil maxValue totalLength str =
  pure $ if totalLength <= maxValue
    then Continue (sumLength totalLength str)
    else Done totalLength

test_sumLengthUntil : Test
test_sumLengthUntil = do
  assertEq 7 $
    reduce (MkReducer () (sumLengthUntil 5) (const id)) 0 ["abc", "de", "", "fg", "hij"]

--------------------------------------------------------------------------------

sumSquaresOfOdds : List Int -> Int
sumSquaresOfOdds = transduce (filtering odd . mapping (\x => x * x)) (+) 0

test_sumSquaresOfOdds : Test
test_sumSquaresOfOdds =
  assertEq (1 + 9 + 25 + 49 + 81) $ sumSquaresOfOdds [1..10]

--------------------------------------------------------------------------------

unwordSmallNames : Nat -> List String -> String
unwordSmallNames maxLength strings =
  transduce (filtering smallStrings . interspersing " ") (++) "" strings
  where smallStrings s = length s <= maxLength

test_unwordSmallNames : Test
test_unwordSmallNames =
  assertEq "a bbbb ddd e" $ unwordSmallNames 4 (words "a bbbb ccccc ddd e")

--------------------------------------------------------------------------------

startsWith : Char -> String -> Bool
startsWith c str =
  if length str == 0 then False else strHead str == c

--------------------------------------------------------------------------------

export
run_tests : IO ()
run_tests =
  noReport $ runTestSuite [
    test_sumSquaresOfOdds,
    test_unwordSmallNames,
    test_sumLength,
    test_sumLengthOfEveryOddStrings]

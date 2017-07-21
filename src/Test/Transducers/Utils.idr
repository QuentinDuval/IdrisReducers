module Test.Transducers.Utils

%access public export

Test : Type
Test = IO Int

assertThat : Bool -> String -> Test
assertThat test errorMsg =
  if test
    then do putStrLn "Test Passed"; pure 0
    else do putStrLn ("Test Failed: " ++ errorMsg); pure 1

assertEq : (Eq a, Show a) => (expected : a) -> (given : a) -> Test
assertEq e g =
  assertThat (g == e) $
    "Expected == " ++ show e ++ ", Got: " ++ show g

runTestSuite : (List Test) -> Test
runTestSuite = foldl (\res, t => (+) <$> res <*> t) (pure 0)

noReport : Test -> IO ()
noReport test = do test; pure ()

odd : Int -> Bool
odd n = mod n 2 == 1

twice : Int -> List Int
twice = replicate 2

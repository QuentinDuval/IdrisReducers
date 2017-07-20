module Test.Transducers.Core

import Transducers
import Test.Transducers.Utils


--------------------------------------------------------------------------------
-- Unit tests
--------------------------------------------------------------------------------

should_map : List Int -> IO ()
should_map input =
  assertEq
    (foldl (+) 0 (map (*2) input))
    (transduce (mapping (*2)) (+) 0 input)

should_follow_map_law : IO ()
should_follow_map_law =
  assertEq
    (transduce (mapping length . mapping (*2)) (+) 0 ["abc", "", "cdef", "g"])
    (transduce (mapping ((*2) . length)) (+) 0 ["abc", "", "cdef", "g"])

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

should_reduce_terminal : List Int -> IO ()
should_reduce_terminal input =
  assertEq
    (foldl (+) 0 (filter odd (map (*2) input)))
    (reduce (mapping (*2) . filtering odd $ terminal (+)) 0 input)

should_take : List Int -> IO ()
should_take input =
  assertEq
    (foldl (+) 0 (take 10 input))
    (transduce (taking 10) (+) 0 input)

{-
should_take_while : IO ()
should_take_while =
  assertEq 21 $ transduce (takingWhile (< 17)) (+) 0 [1..100]
-}

should_drop : List Int -> IO ()
should_drop input =
  assertEq
    (foldl (+) 0 (drop 10 input))
    (transduce (dropping 10) (+) 0 input)

should_pipe_from_left_to_right : List Int -> IO ()
should_pipe_from_left_to_right input =
  assertEq
    (foldl (+) 0 (map (+1) (concatMap twice (filter odd input))))
    (transduce (filtering odd . catMapping twice . mapping (+1)) (+) 0 input)

should_allow_pure_xf_composition : IO ()
should_allow_pure_xf_composition = do
    assertEq 50 (transduce xf1 (+) 0 [1..100])
    assertEq 30240 (transduce xf1 (*) 1 [1..100])
    assertEq 0 (transduce (mapping (fromNat . length) . xf1) (+) 0 (replicate 100 "ab"))
    assertEq 0 (transduce (xf2 . mapping fromNat . xf1) (+) 0 (replicate 100 "ab"))
  where
    xf1 : Transducer s (Nat, s) Int Int
    xf1 = taking 10 . filtering odd . mapping (*2)

    xf2 : Transducer s s Nat String
    xf2 = mapping length

should_index : IO ()
should_index = do
    assertEq "0: Zero, 1: One, 2: Two" (transduce xf (++) "" ["Zero", "One", "Two"])
  where
    xf : Transducer s (Int, Bool, s) String String
    xf = indexing . mapping (\(idx, s) => show idx ++ ": " ++ s) . interspersing ", "


should_chunk_of : IO ()
should_chunk_of = do
    assertEq "abcd efgh ijkl " (transduce xf (++) "" ['a'..'l'])
    assertEq "abcd efgh ij " (transduce xf (++) "" ['a'..'j'])
  where
    xf : Transducer s (List Char, s) String Char
    xf = chunksOf 4 . mapping pack . mapping (++ " ")

should_intersperse : IO ()
should_intersperse = do
  let cs = ["a", "list", "of", "words"]
  assertEq "a, list, of, words" (transduce (interspersing ", ") (++) "" cs)

should_deduplicate : IO ()
should_deduplicate = do
  assertEq "abcdcbad" $ transduce (mapping singleton . deduplicate) (++) "" (unpack "abbcddccbaad")

export
run_tests : IO ()
run_tests = do
  should_map [1..100]
  should_follow_map_law
  should_filter [1..100]
  should_concat_map [1..100]
  should_reduce_terminal [1..100]
  should_take [1..100]
  --should_take_while
  should_drop [1..100]
  should_pipe_from_left_to_right [1..100]
  should_allow_pure_xf_composition
  should_index
  should_chunk_of
  should_intersperse
  should_deduplicate

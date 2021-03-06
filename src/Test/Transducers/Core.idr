module Test.Transducers.Core

import Transducers
import Test.Transducers.Utils


--------------------------------------------------------------------------------
-- Unit tests
--------------------------------------------------------------------------------

should_map : List Int -> Test
should_map input =
  assertEq
    (foldl (+) 0 (map (*2) input))
    (transduce (mapping (*2)) (+) 0 input)

should_follow_map_law : Test
should_follow_map_law =
  assertEq
    (transduce (mapping length . mapping (*2)) (+) 0 ["abc", "", "cdef", "g"])
    (transduce (mapping ((*2) . length)) (+) 0 ["abc", "", "cdef", "g"])

should_filter : List Int -> Test
should_filter input =
  assertEq
    (foldl (+) 0 (filter odd input))
    (transduce (filtering odd) (+) 0 input)

should_concat_map : List Int -> Test
should_concat_map input =
  assertEq
    (foldl (+) 0 (concatMap twice input))
    (transduce (catMapping twice) (+) 0 input)

should_reduce_terminal : List Int -> Test
should_reduce_terminal input =
  assertEq
    (foldl (+) 0 (filter odd (map (*2) input)))
    (reduce (mapping (*2) . filtering odd $ terminal (+)) 0 input)

should_take : List Int -> Test
should_take input =
  assertEq
    (foldl (+) 0 (take 10 input))
    (transduce (taking 10) (+) 0 input)

should_take_while : Test
should_take_while =
  assertEq 55 $ transduce (takingWhile (<= 10)) (+) 0 [1..100]

should_drop : List Int -> Test
should_drop input =
  assertEq
    (foldl (+) 0 (drop 10 input))
    (transduce (dropping 10) (+) 0 input)

should_pipe_from_left_to_right : List Int -> Test
should_pipe_from_left_to_right input =
  assertEq
    (foldl (+) 0 (map (+1) (concatMap twice (filter odd input))))
    (transduce (filtering odd . catMapping twice . mapping (+1)) (+) 0 input)

should_allow_pure_xf_composition : Test
should_allow_pure_xf_composition =
  let xf = taking 10 . filtering odd . mapping (*2)
  in do
    assertEq 50 (transduce xf (+) 0 [1..100])
    assertEq 30240 (transduce xf (*) 1 [1..100])
    assertEq 0 (transduce (mapping length . mapping fromNat . xf) (+) 0 (replicate 100 "ab"))

should_index : Test
should_index = do
  let xf = indexing . mapping (\(idx, s) => show idx ++ ": " ++ s) . interspersing ", "
  assertEq "0: Zero, 1: One, 2: Two" (transduce xf (++) "" ["Zero", "One", "Two"])

should_chunk_of : Test
should_chunk_of = do
  let xf = chunksOf 4 . mapping pack . mapping (++ " ")
  assertEq "abcd efgh ijkl " (transduce xf (++) "" ['a'..'l'])
  assertEq "abcd efgh ij " (transduce xf (++) "" ['a'..'j'])

should_intersperse : Test
should_intersperse = do
  let cs = ["a", "list", "of", "words"]
  assertEq "a, list, of, words" (transduce (interspersing ", ") (++) "" cs)

should_deduplicate : Test
should_deduplicate = do
  assertEq "abcdcbad" $ transduce (mapping singleton . deduplicate) (++) "" (unpack "abbcddccbaad")

should_group_by : Test
should_group_by =
  assertEq ["aa", "b", "ccc", "b"] $
    reverse $ into [] (groupingBy (==) . mapping pack) (unpack "aabcccb")

should_group_by_with_custom_predicate : Test
should_group_by_with_custom_predicate =
  assertEq 3 $ longestIncreasingSeq [1, 2, 1, 3, 4, 1, 5, 3, 4]
  where
    longestIncreasingSeq = transduce (groupingBy (<) . mapping length . mapping fromNat) max 0

should_support_isomorphisms : Test
should_support_isomorphisms =
  assertEq "ei" $
    into "" (under (MkIso ord chr) (mapping (+1)) . filtering vowel) (unpack "abcdefgh")

export
run_tests : IO ()
run_tests =
  runTestSuite [
    should_map [1..100],
    should_follow_map_law,
    should_filter [1..100],
    should_concat_map [1..100],
    should_reduce_terminal [1..100],
    should_take [1..100],
    should_take_while,
    should_drop [1..100],
    should_pipe_from_left_to_right [1..100],
    should_allow_pure_xf_composition,
    should_index,
    should_chunk_of,
    should_intersperse,
    should_deduplicate,
    should_group_by,
    should_group_by_with_custom_predicate,
    should_support_isomorphisms]

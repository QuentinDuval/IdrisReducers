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

should_take : List Int -> IO ()
should_take input =
  assertEq
    (foldl (+) 0 (take 10 input))
    (transduce (taking 10) (+) 0 input)

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
should_allow_pure_xf_composition =
  let xf = taking 10 . filtering odd . mapping (*2)
  in do
    assertEq 50 (transduce xf (+) 0 [1..100])
    assertEq 30240 (transduce xf (*) 1 [1..100])

should_index : IO ()
should_index = do
  let xf = indexing . mapping (\(idx, s) => show idx ++ ": " ++ s) . interspersing ", "
  assertEq "0: Zero, 1: One, 2: Two" (transduce xf (++) "" ["Zero", "One", "Two"])

should_chunk_of : IO ()
should_chunk_of = do
  let xf = chunksOf 4 . mapping pack . mapping (++ " ")
  assertEq "abcd efgh ijkl " (transduce xf (++) "" ['a'..'l'])
  assertEq "abcd efgh ij " (transduce xf (++) "" ['a'..'j'])

should_intersperse : IO ()
should_intersperse = do
  let cs = ["a", "list", "of", "words"]
  assertEq "a, list, of, words" (transduce (interspersing ", ") (++) "" cs)

export
run_tests : IO ()
run_tests = do
  should_map [1..100]
  should_filter [1..100]
  should_concat_map [1..100]
  should_take [1..100]
  should_drop [1..100]
  should_pipe_from_left_to_right [1..100]
  should_allow_pure_xf_composition
  should_index
  should_chunk_of
  should_intersperse

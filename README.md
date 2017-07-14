# Idris Transducers

Implementation a transducer-like library in Idris, inspired by the great Clojure transducer library: https://clojure.org/reference/transducers.

## Goal & Motivation

The goal is to provide transformation of accumulating functions that:

* Can be composed together as transformation pipe
* Do not suffer from the overhead of creating intermediary lists
* Can support arbitrary inner state (for non trivial transformations)

## Example

Here are some examples of transformations we can write:

    -- Standard Idris (creating intermediary lists)
    foldl (+) 0 (map (+1) (concatMap twice (filter odd [1..100])))

    -- Using the reducer library
    transduce (filtering odd |> catMapping twice |> mapping (+1)) (+) 0 [1..100]

The above code takes as input a list of integers between 1 and 100, and:

* Filter the odd numbers out of it
* Repeat of each of these number twice
* Add one to each numbers
* Sum them all

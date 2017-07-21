# Idris Transducers

[![Build Status](https://travis-ci.org/QuentinDuval/IdrisReducers.svg?branch=master)](https://travis-ci.org/QuentinDuval/IdrisReducers)

Implementation a transducer-like library in Idris, inspired by the great Clojure transducer library: https://clojure.org/reference/transducers.

## Goal & Motivation

The goal is to provide transformation of accumulating functions that:

* Can be composed together as transformation pipe
* Do not suffer from the overhead of creating intermediary lists
* Can support arbitrary inner state (for non trivial transformations)

## Examples

Here is a first example of transformations we can write:

* Take a collection as input
* Keep only the odd numbers
* Repeat these numbers twice (twice is `replicate 2`)
* Sum the resulting stream of integer values

This would look like this:

    -- Standard Idris (creating intermediary lists)
    foldl (+) 0 (map (+1) (concatMap twice (filter odd [1..100])))
    
    -- Using the transducers
    transduce (filtering odd . catMapping twice . mapping (+1)) (+) 0 [1..100]

These transformations do not realize intermediary lists, and do not necessarily consume the entire stream of values. The stream is consumed lazily. The code below will execute much faster with transducers:

    -- Standard Idris (not lazy: mapping 1000 values)
    foldl (+) 0 (take 10 (map (+1) [1..1000]))

    -- With the transducers (lazy: mapping 10 values)
    transduce (mapping (+1) . taking 10) (+) 0 [1..1000]

We can also add stateful transformations in the pipe, such as one that remove adjacent duplicated elements:

    transduce (mapping singleton . deduplicate) (++) "" (unpack "abbcddccbaad")
    > "abcdcbad"

* `mapping singleton` transforms every character into a string
* `deduplicate` removes adjacent duplicated elements

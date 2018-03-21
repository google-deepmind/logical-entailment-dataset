# Entailments for Propositional Logic.

This repository contains an entailment dataset for propositional logic, and code for generating that dataset.
It also contains code for parsing the dataset in python.

See the ICLR paper: https://openreview.net/pdf?id=SkZxCk-0Z

## The dataset

The dataset is in the data directory.

## How to build this code

Install Haskell. Then...

1. cabal configure
1. cabal build
1. cabal install

## How to run this code

1. dist/build/entailment/entailment

This will generate a file called four_tuples.txt containing the entailments.

Each line in the file is a tuple (A, B, E, H1, H2, H3) where:
  * A and B are propositions
  * E is an integer (1 or 0) indicating whether A entails B (written A ⊧ B)
  *  H1, H2, and H3 are statistics for simple heuristic estimates
        * H1 = whether length(A) >= length(B)
        * H2 = whether vars(B) ⊆ vars(A)
        * H3 = whether literals(B*) ⊆ literals(A*)
            (where A* is negation-normal-form version of A)

The crucial pieces of information are the two propositions (A and B) and the entailment E. 

## Command-line arguments

When running, there are various command-line parameters you can use:
  * first arg: number of pairs to generate
  * second arg: max number of variables in a formula
  * third arg: max complexity of a formula

NB four-tuples are extracted from generated pairs. But many pairs are unsuitable for four-tuples. So if you want 100 entailment lines, you need 100/4 = 25 four-tuples,  and you might need 200 pairs to produce 25 four-tuples. The ratio of pairs-to-four-tuples is not constant, and depends on the complexity of the formulas.

## Parser

A python parser for this dataset is included in parser.py



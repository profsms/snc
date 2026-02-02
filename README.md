# Seymour's Second Neighborhood Conjecture — Computational Study for $n\le7$

This repository contains Julia code supporting the results of the paper

> *Seymour’s Second Neighborhood Conjecture for Graphs of Order $\le7$ (and Split–Twin Extensions)*  
> (In review)

The code implements:
- exhaustive verification of the second neighborhood property for small oriented graphs,
- guided sampling for larger graphs,
- structural filtering and invariant analysis.

## Requirements
- Julia ≥ 1.9

## Usage
Each script can be run independently. For example:

```bash
julia src/exhaustive_ratios.jl 7
julia src/guided_sampling.jl 10

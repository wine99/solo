# Solo: A Lightweight Static Analysis for Differential Privacy

----

# Abstract
Differential Privacy is a fairly recent technique used to protect privacy of individuals when performing statistical analysis. The core idea is to add noise to queries to ensure that it is hard to figure out what each individual has contributed to the result. We introduce our implementation of Solo, a framework that facilitates writing differentially private queries in Haskell. Solo is able to track differential privacy parameters at the type level, and enforce privacy *before* a query is run. We implement noise-injecting mechanisms, including the Laplace Mechanism, Gaussian mechanism, and the Exponential mechanism, and we implement several primitives that analysts can use to write queries. Lastly, we experiment with our implementation by looking at how we can compute a CDF, and how we can find the most frequently occurring element from a list.


# How to run
Main.hs contains examples of computing CDF and finding the most frequent number in a list.
One may run this via the command 
```
stack run
```

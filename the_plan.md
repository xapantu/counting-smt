---
author: Lucas
date: 6/6/2014
title: The Plan
---

The Problem
===========


The Solution (1)
================

* counting for arrays
* restrict our case to arrays with a finite domain (booleans)
* splitting them with the assumptions made by the model
* this in the smt preprocessor written in OCaml (codename counting-smt)

The Solution (2)
================

* first check that this property probably holds in bmc.
* second strengthen it so as it is provable via kind.
* fix sally so as IC3 works with generic smtlib solvers (once the yices-specific bits are sorted out)
* come up with a plan for IC3 with arrays (as in check there is no surprise)
* solve it automatically

The Solution (3)
================

four subsolutions

* implement that in yices
* implement that in z3 (?)
* implement an api in counting-smt
* forget about speed





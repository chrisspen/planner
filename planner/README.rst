=======================================================================
title - An automated Python planning engine.
=======================================================================

Overview
========

Installation
------------

Usage
-----

Applying the engine to solve your own problem involves creating three components.

* domain
  This defines rules describing how states change when actions are applied, as well as a fitness function which rate's the state's overall completion of the goal.

* problem
  Describes a specific initial state from where the planner should start searching for the goal, as well as how you would like to interface with the planner.

* module
  This is an optional Python module that defines special domain-specific functionality accessible to the planner. Effectively anything accessible from Python can be placed or referenced from here.

Design Goals
------------

Listed in order of perceived importance. Results may vary.

* Intuitive
  The system should be simple to use and easy to understand.

* Real-time
  The system should be able to maintain a "real-world" state, be able to incorporate incremental changes to this state as they occur in the real-world, and reuse internal planning data to avoid re-planning from scratch.

* Uncertainty
  The system should be able to model and reason over uncertain state transitions.

* Small Memory Footprint
  The system should not use huge amounts of memory. When constructing the state transition graph, state nodes should not store any facts. When a new state is created, its facts should be converted to a hash, which will be used to universally identify this state. Only a differential list of facts added and removed when transitioning between states should be stored in a state.

  When possible, the system should attempt to identify dependencies and relationships between state features, and represent this relationships as state hierarchies.

* Fast
  The system should find a good, but not necessarily optimal solution, in a reasonable amount of time.

History
-------


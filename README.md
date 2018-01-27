Planner - A simple Python real-time best-first planning algorithm
=================================================================

[![Build Status](https://img.shields.io/travis/chrisspen/django-chroniker.svg?branch=master)](https://travis-ci.org/chrisspen/django-chroniker)

Overview
--------

This package implements a basic [A-star](http://en.wikipedia.org/wiki/A*_search_algorithm) planning algorithm that takes
a problem domain and problem instance and returns a list of actions necessary to solve a goal.

I've borrowed heavily from the [STRIPS](http://en.wikipedia.org/wiki/STRIPS) and [PDDL](http://en.wikipedia.org/wiki/Planning_Domain_Definition_Language)
planning domain language styles so anyone familiar with these should find the basic architexture familiar.

It supports a form of "soft" real-time planning by efficiently caching calculated future states and using them
to prevent redundant state evaluation after the current state changes. To do this, it stores links between the current state
and all derived states.
When the current state changes, all states not linked to the new current state are pruned and removed from the planner's priority heap.
The plan() method, which evaluates the next state in the priority heap, is implemented as a generator, so the planning can be ran, paused,
and resumed simply by controlling how often you iterate over the generator. Each iteration of the plan() generator results in an 
evaluation of a single state
and the deposit of all potential derived states into the planner's priority queue for future evaluation. It's left up to the
developer to decide when and how they want to call plan() so as to plan in real-time (e.g. by running the method in a background thread).

Since some domains could theoretically have an arbitrarily large or infinite search space, the planner can be configured to run
until no improvement to the fitness function is found after a certain number of cycles.

To conserve memory, only the set of facts in the state currently being evaluated are explicitly stored.
All other facts in all other states are represented as a network of nodes linked by differential actions describing the facts
that are added or removed to achieve the state in relation to the current state.

Using this network, the planner can store an extremely large
set of states, achieving great breadth and depth while minimizing memory usage. The main downside to this design
is that in order to switch between states, the planner must lookup the series of differential actions necessary to
translate the current state to the next state in the heap. If these states are very different, this sub-search could take a while.
However, in practice, these states are usually very similar, resulting in a relatively fast switch.

Installation
------------

This package uses Clips as its [RETE](http://en.wikipedia.org/wiki/Rete_algorithm>) engine, so you'll need to install
the appropriate [Clips](http://clipsrules.sourceforge.net/) and [PyClips](http://pyclips.sourceforge.net/web/) packages for your platform.

On Ubuntu, you can install Clips via::

    sudo apt-get install clips

Before installing PyClips, you'll need dependencies for building Python C-extensions.
On Ubuntu, you can install these via::

    sudo apt-get install build-essential python-dev
    
Then you can build and install PyClips with pip via::

    sudo pip install https://sourceforge.net/projects/pyclips/files/pyclips/pyclips-1.0/pyclips-1.0.7.348.tar.gz/download

Finally, install the package via pip with::

    sudo pip install https://github.com/chrisspen/planner/tarball/master
    
Usage
-----

To use this package, you first define a "domain", either programmatically via a Python script or via a YAML file. This definition includes:

1. A series of operators describing how an action modifies the state.
2. A fitness function that estimates how close the current state is to the "solution" state.

Next, you define a series of facts that describe a specific problem, or "starting state", in this domain.

Both domains and problems can be created programmatically and saved to a YAML file, and later reloaded.
Previous versions stored serialized data as S-expressions, similar to legacy STRIPS/PDDL planners,
but this has been deprecated.

Note, the fitness function should be generic and not include any problem-specific facts. In the blocks world example, you'd define facts representing
the "current" and "goal" states. The fitness function would then calculate how many of the goal facts match the current facts, returning a score
proportional to how many goals are met (e.g. 0=no goals are met, 0.5=half of goals are met, 1.0=all goals met).

For example domains, see the "tests" folder.

Testing
-------

To run unittests across multiple Python versions, install:

    sudo add-apt-repository ppa:deadsnakes/ppa
    sudo apt-get update
    sudo apt-get install python-dev python3-dev python3.4-minimal python3.4-dev python3.5-minimal python3.5-dev python3.6 python3.6-dev

To run all unittests:

    tox

To run all unittests for a specific Python version:

    unset TESTNAME; tox -e py27

To run a specific test for a specific Python version:

    export TESTNAME=planner.tests.test_driving.Test.test_driving; tox -e py27

Future
------

- Probability
    Since most "real world" domains include noisy environments, the operators should be able to model the probability
    of various mutually-exclusive states occurring,
    and use this probability to direct the planner to the most likely states.
    There's already some basic framework for this in the code, but it hasn't been fleshed out or tested with a practical domain.

- Learning
    Currently, all operators (i.e. transitions) are manually defined as hard-coded production rules.
    I'd like to support an interface for "plugging in" an arbitary model learner that can observe and record state features, learn a model,
    and generate the appropriate operators.
    
- Relational Planning
    A big scalability limitation with the STRIPS style of planners is how they represent their operators and facts as relatively
    "flat" lists of items,
    with little to no hierarchy or organization. As the list of operators and facts grows, they become unweildy and difficult
    to debug when their behavior doesn't match your expectations.
    Unfortunately, adding support for relational data, relational MDPs, schema or object-oriented structure in planners is
    still an area of active research.

- Database
    Most non-trival systems dealing with large amounts of information store their data in a SQL database.
    Unfortunately, nearly all RETE engines only operate on data loaded into memory, limiting the number of rules and facts it can
    reason over at any given time.
    I'd like to bridge this divide by allowing the planner to directly retrieve facts from a SQL database
    and gracefully handle offloading of unused rules and facts from memory.
    

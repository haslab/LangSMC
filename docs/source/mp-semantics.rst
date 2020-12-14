Multi-party semantics
========================

The multi-party semantics class establishes how a program can
be collaboratively animated. We define the multi-party semantics
assuming that program evaluation is carried out by three computing
nodes, each one holding a description of the program in pottentially
different languages ``L1``, ``L2`` and ``L3``. We restrict the multi-party semantics
to only three parties due to tool limitations. Nevertheless,
having a three-party set is explanatory enough to demonstrate
the concepts we want to explore in this work and the definitions
here presented can be easily extended to other party configurations.

Our multi-party semantics formalization is based on adversarial code,
influenced by the UC model. Program evaluation is managed
by an *environment*, that can provide inputs to the program
being interpreted and also collect outputs at any time.
Furthermore, the environment can request the evaluation of
the program in a small-step basis. This evaluation is carried
out by an *adversary*, that, at a high-level, models the
inside behaviour of the *environment* inside the program
execution.

The *adversary* has the possibility of either request some local party
execution or a synchronised execution, where all parties, executing
at the same time, have the ability to perform distributed protocols
that require party interaction.

Finally, the semantics here specified contemplates the possiblity
of the execution disclosing the communication trace that
is left by operations that result from the collaboration of parties.

Semantics interface
-------------------------

The semantics interface discloses 6 procedures:
* ``init(P)`` - initialises the evaluation with initial program P
* ``stepP(id)`` - localy executes party ``id``.
* ``stepS`` - executes the entire set of
parties at the same time. This procedure should be used to perform
operations that require party synchronisation.
* ``stepInput(x)`` - processes the input ``x`` provided by the environment
* ``getOutput`` - releases output to the environment

::

  module type Semantics = {
    proc init(P1 : L1.L, P2 : L2.L, P3 : L3.L) : unit
    proc stepP(id : partyId_t) : bool
    proc stepS() : sideInfo_t option
    proc setInput(x : secret_t) : bool
    proc getOutput() : secret_t option
  }.

We enforce that the only procedure inside the multi-party semantics
that is able to generate visible side information is the synchronized
``stepS`` method. Local party execution modeled by ``stepP`` does not
encompass any visible information, as it simply computes some local
operation.

Environment interface
-------------------------

The environment semantics interface specifies how the environment
interacts with the program evaluation. It discloses 3 procedures:
* ``stepInput(x)`` - provides input ``x`` to the program semantics
* ``getOutput`` - collects output from the program
* ``activate`` - activates the adversary so that it can procede with the actual program evaluation.

::

  module type EnvSemInterface = {
    proc setInput(x: secret_t): bool
    proc getOutput(): secret_t option
    proc activate(): sideInfo_t option
  }.

The environment has oracle access to the environment semantics
interface in order to animate some program via the ``animate``
procedure. To represent the output of some program animation, we
enrich the formalization with a special ``output_event_t`` type.

::

  module type Environment (ESI: EnvSemInterface) = {
    proc animate(): output_event_t 
  }.

Adversary interface
-------------------------

The adversary semantics interface specifies how the adversary
interacts with the program evaluation. It discloses 2 procedures: 
- ``stepP(id)`` - locally executes party ``id``
- ``stepS`` - performs a synchronised execution of the entire set of parties

::

  module type AdvSemInterface = {
    proc stepP(id: partyId_t): bool
    proc stepS(): sideInfo_t option
  }.

The adversary has oracles access to the adversary semantics interface
in order to execute one instruction of a program via the ``step``
procedure.

::

  module type Adversary (ASI : AdvSemInterface) = {
    proc step() : sideInfo_t option
  }.

General evaluation strategy
----------------------------------

Armed with the structures previously defined, we can now construct a
general evaluation strategy that executes any given program and that
ends with the output event that is verified by the *environment*.

We start by specifying a concrete implementation of the *environment*
semantics oracle that is parameterized by the concrete semantics of
the program and by an adversary. This new module
``EnvironmentSemanticsInterface`` essentially defines all possible
*enviornment* operations based on the concrete semantics of the
program and based on the evaluation strategies disclosed by the
adversary.

::

  module EnvironmentSemanticsInterface (Sem : Semantics) (A : Adversary) = {
    include Sem [-init, setInput, getOutput]
    proc init = Sem.init
    proc setInput (x: secret_t): bool = {
      var r;
      r <@ Sem.setInput(x);
      return r;
    }
    proc getOutput(): secret_t option = {
      var r;
      r <@ Sem.getOutput();
      return r;
    }
    proc activate(): sideInfo_t option = {
      var r;
      r <@ A(Sem).step();
      return r;
    }
  }.

Finally, a program can be computed according to the generic procedure
displayed bellow. It takes as input 3 programs written in languages
``L1``, ``L2`` and ``L3``, initializes the local semantics module of
each party with the respective program and
then proceeds with the concrete program execution. It adopts as output
the same output given to by the *environment*.

::

  module Eval(Sem : Semantics, Z : Environment, A : Adversary) = {
    proc eval(P : L) = {
      var b;
      EnvironmentSemanticsInterface(Sem,A).init(P);
      b <@ Z(EnvironmentSemanticsInterface(Sem,A)).animate();
      return (b);
    }
  }.

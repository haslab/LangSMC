Single-party semantics
========================

The single-pary semantics class is parameterised by a language and
should establish how programs written in that language are animated as
if they were being executed in a idealized way by a TTP.

Our sigle-party semantics formalization is based on adversarial code,
influenced by the UC model. Program evaluation is managed
by an *environment*, that can provide inputs to the program
being interpreted and also collect outputs at any time.
Furthermore, the environment can request the evaluation of
the program in a small-step basis. This evaluation is carried
out by an *adversary*, that, at a high-level, models the
inside behaviour of the *environment* inside the program
execution.

The *adversary* has the possibility of requesting the execution of one
program statement at a time. The semantics also contemplates the
possiblity of some side information ``sideInfo_t`` being leaked by the execution of
language instructions.

Our EasyCrypt single-party semantics formalization is based on the
EasyCrypt's module system, that allows the definition of *signature
types* for procedures by using *module type* EasyCrypt structure.

Semantics interface
-------------------------

The semantics interface discloses 6 procedures:
* ``init(P)`` - initialises the evaluation with initial program P
* ``step`` - sequential semantics procedures, that executes one instruction of the program.
* ``stepInput(x)`` - processes the input ``x`` provided by the environment
* ``getOutput`` - releases output to the environment

::

  module type Semantics = {
    proc init(P : L) : unit
    proc step() : sideInfo_t option
    proc setInput(x : secret_t) : bool
    proc getOutput() : secret_t option
  }.

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
    proc step(): sideInfo_t option
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
    proc init = Sem.init
    proc setInput(x: secret_t): bool = {
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
displayed bellow. It takes as input a program written in any language
``L``, initializes the semantics module with the concrete program and
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

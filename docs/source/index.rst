.. LangSMC documentation master file, created by
   sphinx-quickstart on Mon Dec 14 01:21:09 2020.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

LangSMC documentation
===================================

**LangSMC** is a formalisation effort whose goal is to machine-check
the connection between verified compilation and cryptographic security
that is verified inside secure multiparty computation (SMC)
frameworks. The documentation here displayed can be matched to the
formal definitions and results described in [link para o artigo eprint].

Project introduction
==================================

Secure multiparty computation (SMC) is a cryptographic technology
that enables mutually distrusting parties to jointly
perform computations while retaining control over their secret
inputs. A solid theoretical foundation supports SMC, establishing 
feasibility and impossibility results for general secure computation
over many dimensions of the design space, including 
the number of parties, % (2-party vs $n > 2$ parties is a common distinction), 
the class of computations, the trust model and the power of attackers.

In the last decade, efficient protocols have been developed and optimised 
for specific design goals (concrete computations, restricted
classes of attackers, etc.). 
These protocols were successfully deployed in a number of real-world 
scenarios. In this project, we consider a class of SMC protocols that, due 
to its efficiency and generality, has received significant
attention from the academic community and industry
alike. These protocols are built on top of linear 
secret sharing, which underlies several of the state-of-the-art
SMC frameworks in the literature, such as *Sharemind*,
*SCALE-MAMBA*, *SPDZ*, *FRESCO*, *PICCO* or *JIFF*.

We consider core transformations that such frameworks must
deal with. The overarching goal is to allow (possibly non-expert) developers to program
particular applications via a high-level specification language that
hides the low-level details of the secure computation protocols underneath.
At this level, public and secret data are seen as inhabitants of data types
in a high-level language; computations over secret data are idealised/modularised
as calls to an an *ideal* static library as if they were performed in the clear by a 
trusted third-party (TTP). SMC tool-chains usually provide implementations
of the semantics of these ideal-world libraries that developers can use
to animate and debug their high-level computation specifications.

The role of the framework is then to compile such idealised specifications
into framework-specific executable code for the various parties.
This code will orchestrate calls to a distributed static library that
implements low-level SMC protocols for each of the operations idealised,
and thus allow the different parties to collaboratively carry out the computation
over secret-shared data.Conceptually, such frameworks are carrying out two types of
transformations:

1. Replacing the semantic domain of secret data from idealised TTP-like 
processing to real-world secret-shared
data processing.
2. taking a program in high-level language and transforming it into a collection of communicating programs 
that the various parties can execute, either in the same low-level language 
or in different low-level languages.

The tool-chains in existing SMC frameworks are crafted to demonstrate
cryptographic advances, such as a new SMC protocol, or novel program 
analysis or transformations, such as a type system or a code optimisation;
a recent literature review frames this area of
research as follows:

  Programming languages is a field dedicated to creating compilers but little SMC research leverages these techniques. [...] However, the SMC community would benefit if frameworks took a more principled approach to language design and verification.

We argue that the way to fill this gap is to split
the problem of secure compilation for SMC across the two dimensions
previously identified, and ask the following question:

  Can one decompose the problem of secure compilation for SMC into two orthogonal dimensions - source-to-target language semantic gap and ideal-to-real world security gap - so that compilation tools can be analysed independently for each type of transformation?

We frame this question by proposing a language-based execution model that exposes this 
duality (LINK TO DOCUMENTATION SECTION).
Here, ideal computations are expressed as the evaluation of a program under the
semantics of a programming language and makes calls to an external 
static library; this static library defines the low-level computations that can be
performed securely using (atomic) MPC protocols.
This view of ideal functionalities is fully general, and may be of independent 
interest.

We then formalize a framework for program-based secure computation 
(LINK TO DOCUMENTATION SECTION) that can be parameterised with an arbitrary 
secure computation library (LINK TO DOCUMENTATION SECTION). 
We adopt a notion of secure MPC libraries that is inspired by the *Sharemind*
framework in that we allow for low-level protocols to offer only
a weak form of security known as *privacy*, but still require the 
full protocol to be secure in a standard UC sense. This allows our
framework to preserve the strong composition guarantees ensured by
protocols shown to be UC secure. Moreover, our execution model implicitly assumes global synchronisation 
points between computing  parties when executing low-level protocols. In this 
first step we also limit our  attention to passive security and static corruptions.

We answer the question by showing how a secure compilation 
framework may follow any path to guarantee the security of the generated 
protocols. Along the way, we identify sufficient conditions on the components 
of the framework that clearly expose the duality between
the programming languages (LINK TO DOCUMENTATION SECTION horizontal) and the cryptographic security
domains (LINK TO DOCUMENTATION SECTION vertical):

* Vertically, we prove that, under natural assumptions on the
  language and the static libraries, a secure compiler that
  replicates the ideal program to all computing parties and replaces the
  ideal static library with a secure distributed one is guaranteed to
  produce a secure SMC protocol (LINK TO DOCUMENTATION SECTION horizontal). We adopt
  the standard notion of Universal Composability (UC) security for SMC 
  protocols in the presence of passive adversaries and static 
  corruptions; we consider reactive functionalities that can perform 
  input/output operations with the parties at any time during its execution
  in the style of Arithmetic Black-Box (ABB).
* Horizontally, we prove that the trace-preservation properties
  offered by general-purpose certified compilers such as
  *CompCert* are sufficient to make our diagram commute, by
  either changing the language in the ideal world or in the real world,
  where parties may independently compile their local program copies.


.. toctree::
   :maxdepth: 2
   :caption: Contents:

   proof-overview
   abstract-classes
   sp-semantics
   mp-semantics
   secure-api
   sp-api-semantics
   mp-api-semantics
   protocol-api
   sp-protocol-api-semantics
   mp-protocol-api-semantics



Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`

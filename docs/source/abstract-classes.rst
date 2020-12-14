Abstract components
============================

Our formalization makes use of some abstract definitions for general
purpose components that are required by our proof. These include an
abstract formalization of a programming language and of a secret
sharing scheme. These two constructions are purposely left abstract in
order to demonstrate the modularity of our proof, capable of
supporting any programming language and any instantiation of a secret
sharing primitive.

Programming language construction
--------------------------------------

Our programming language construction provides an interface
disclosing:

Language::

  type L.

Public values::

  type public_t.

Secret values::

  type secret_t.

Secret operators::

  type sop_t.

Input format::

  type inputs_t.

Output format::

  type outputs_t.

Note that we do not provide an explicit distinction between secret and
public operators, as the latter can be defined as program statements
without loss of generality. Moreover, note that our language
abstraction does not impose any restriction on the programs it
tolerates, as languages are abstracted via a single type ``L``. 

Secret sharing scheme construction
------------------------------------

A secret sharing scheme is a cryptographic primitive whose goal is to
"split" some value into *n* shares, such that the knowledge of *t*
shares (*t* < *n*) does not reveal any sensitive information about the
original value that was shared.

Our secret sharing scheme construction provides an interface
disclosing:

Party identifier::

  type partyId_t.

Number of parties::

  op n : int.

Threshold of (tolerated) corrupt parties::

  op t : int.

Values::

  type value_t.

Individual shares::

  type share_t.

Set of all shares::

  type sharedValue_t = share_t list.

Shares a value among n-shares::

  op [lossless] nshr : int -> value_t -> sharedValue_t distr.

Unshares a shared value::

  op unshr: sharedValue_t -> value_t.

The sharing algorithm is classically defined as a probabilistic
algorithm, a condition required in order to ensure the security of the
operation. We model such probabilistic behaviour by encapsulating the
``nshr`` operator around the EasyCrypt special distribution type
``distr``. Informally, this means that sharing some value is essentially
sampling from a distribution space containing all possible sharings
of the value one intends to share. Note that the reconstruction
operator ``unshr`` is a deterministic operator, as it must successfully
reconstruct some value without requiring any secret information.

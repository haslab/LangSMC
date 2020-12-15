Abstract components
============================

Our formalisation makes use of some abstract definitions for general
purpose components that are required by our proof. These include an
abstract formalisation of a programming language, of a secret
sharing scheme and of a *protocol library*, i.e., a collection of
secure protocols that can be used to evaluate secure computations done
when executing a program. These three constructions are purposely left abstract in
order to demonstrate the modularity of our proof, capable of
supporting any programming language, any instantiation of a secret
sharing primitive and any secure protocol library.

Programming language construction
--------------------------------------

The programming language construction provides an interface
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

The secret sharing scheme construction provides an interface
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

Protocol library construction
------------------------------------

The protocol library construction provides an interface disclosing:

The protocol library construction provides a set of secure
protocols that can be used to compute operations over
confidential data, disclosing:

Number of parties involved in the protocol::

  op n : int.

Type of party identifiers::

  type partyId_t. 

Raw (public) values::

  type value_t.

Secret inputs::

  type inputs_t.

Secret outputs::

  type outputs_t.

Messages::

  type msg_data.

Traces (lists of messages)::

  type trace_t = msg_data list.

Information revealed by protocol execution::

  type leakage_t.

Side information represents side information that is passed around
(e.g. leakage or communication traces)::

  type sideInfo_t = { leakage: leakage_t option ; trace: trace_t }.

Secret operators::

  type sop_t.

Functionality of secret operators::

  op sop_spec (sop: sop_t, pargs: value_t list, sargs: value_t list) : value_t * leakage_t option.

Protocols
^^^^^^^^^^^^^^^

Declassification protocol::

  op [lossless] prot_declass(a: inputs_t): (value_t * sideInfo_t) distr.

Input protocol::

  op [lossless] prot_in(inp: inputs_t): sideInfo_t distr.

Output protocol::

  op [lossless] prot_out(a: inputs_t): (outputs_t * sideInfo_t) distr.

Secret operator protocol::

  op [lossless] prot_sop(sop: sop_t, pargs: value_t list, sargs: inputs_t list)
        : (outputs_t * sideInfo_t) distr.


Besides dealing with secret data, protocols also tolerate plain
values, that are assumed to be publicly known to all
parties. Additionally, it is assumed that protocols can leave a
communication trace resulting from party interaction.

The library also provides a set of simulators that are
part of the security assumpiton made over the multiparty
protocols: the protocol is secure if there exists a simulator
that is able to reproduce the communication trace and output
shares of the corrupt parties.

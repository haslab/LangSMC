Secure computation API
===============================

An API is an entity that is capable of performing confidential
computations. It has the ability to manage both public and 
secret data and some computations inside the API may disclose
side information that is publicly visible.

An API may also maintain some internal memory storage, which it
may use to store variables whose values are intended to be secret.

API interactions are made via the construction of API calls and
the result of some API computation can be collected via API
responses. These interactions are made via an interaction buffer,
used both for calls and responses.

The API is also responsible to deal with input and output operations.

API types and operations
-------------------------------------

Our API construction provides an interface disclosing:

Public data type::

  type public_t.

Input and output type::

  type inputs_t.
  type outputs_t.

Secret variables::

  type svar_t. 

Secret operations::

  type sop_t.

Side information::

  type sideInfo_t.

API calls::

  type apiCall_data.

API responses::

  type apiRes_data.

Interaction buffer, both for API calls and responses::

  type apiCallRes.

Extracts some API call from the interaction buffer::

  op apiCall (x: apiCallRes) : apiCall_data option.

Extracts some API response from the interaction buffer::

  op apiRes (x: apiCallRes) : apiRes_data option.

Handle generator
-------------------------

The management of secret data inside the API is done via *handles*
that point to some secret variable. To generate handles, the API can
query the entity depicted bellow that, using the set of existing
handles ``hdls``, generates a new, fresh handle to store some secret
value.

::

  module type Handle = {
    proc create_handle(hdls : svar_t fset) : svar_t
  }.


API module
-------------------------------

A secure computation API discloses the following procedures:
* ``api_init`` - initialises the API engine
* ``api_nparties`` - gets the number of parties that are
interacting with the API
* ``api_sop(sop, pargs, sargs)`` - computes the secret
operation ``sop`` with public arguments ``pargs`` and 
secret arguments ``sargs``
* ``api_declass(a)`` - reveals the secret value of 
variable ``a``, which becomes public.
* ``api_in(xx)`` - adds the input value ``xx`` to the internal
storage of the API
* ``api_out(a)`` - discloses the value of some secret variable ``a``

::

  module type API_t = {
   proc init(): unit
   proc nparties(): int
   proc declass(a: svar_t): (public_t * sideInfo_t) option
   proc input(a: svar_t, inp: inputs_t): sideInfo_t option
   proc output(a: svar_t): (outputs_t * sideInfo_t) option
   proc sop(sop: sop_t, pargs: public_t list, sargs: svar_t list, result: svar_t) : sideInfo_t option
  }.

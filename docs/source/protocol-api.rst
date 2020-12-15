Protocol API
==============================

The protocol API class is an instantiation of a secure computation API that uses
a collection of MPC protocols disclosed by some protocol in order to perform
computations over confidential data.

Although the protocol API we provide here is designed to work
for any protocol library, we differentiate possible protocols that
could comprise the library and that would have different behaviours
in terms of API execution and how the program semantics deals with the 
outputs provided by the API. Particularly, we characterise four protocol instances:

* **sop** protocols - that securely compute some secret operation **sop**
* **declassification** protocols - that declassify some secret value revealing its value
* **input** protocols
* **output** protocols

Inside the API infrastructure, confidential values are stored 
as secret variables, since secret data should not be used in the literal
format.

Realising the secure computation API with the protocol library allows us to provide
concrete instantiations of the types and operators that comprise an API. We start by
realising the ``apiCall_data``. An API call can be either a call to the declassify protocol,
to an I/O operation to a secret operator protocol.

::

  type apiCall_data = [
    | Call_declass of svar_t
    | Call_in of svar_t
    | Call_out of svar_t
    | Call_sop of sop_t & svar_t & value_t list & svar_t list
  ].

Similarly, the API can generate responses to the declassify protocol, to an I/O operation to a secret operator protocol.
Because the responses of secret operator protocols is kept internal to the API, and because I/O protocols do not 
encompass any concrete response at all, we specify the type of API response data with only the type of declassify
outputs ``value_t``.

::

  type apiRes_data = value_t.

The interaction buffers disclosed by the API can be filled either with an API call or with an API response.

::

  type apiCallRes = [
    | ApiCall of apiCall_data
    | ApiRes of apiRes_data
  ].

Lastly, our concrete protocol API also provides methods to collect API calls and to extract API responses from the interaction buffer.

::

  (** Collects an API call from the buffer *)
  op apiCall (x: apiCallRes) : apiCall_data option =
    with x = ApiCall y => Some y
    with x = ApiRes y => None.

  (** Extracts an API response from the buffer *)
  op apiRes (x: apiCallRes) : apiRes_data option =
    with x = ApiCall y => None
    with x = ApiRes y => Some y.

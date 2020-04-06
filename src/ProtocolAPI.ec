(** Concrete API working for an abstract protocol library *)
require import AllCore List.

require import AProtocolLibrary AAPI.

(**
  The protocol API class specifies the behaviour of an API
  executing the MPC protocols disclosed by some protocol library.

  Althogh the protocol API we provide here is designed to work
  for any protocol library, we differentiate possible protocols that
  could comprise the library and that would have different behaviours
  in terms of API execution and how the program deals with the 
  outputs provided by the API.

  Particularly, we characterise four protocol instances:
    - [sop] protocols - that securely compute some secret operation [sop]
    - [declassification] protocols - that declassify some secret value
    revealing its value
    - [input] protocols
    - [output] protocols

  Inside the API infrastructure, confidential values are stored 
  as secret variables, as secret data should not be used in the literal
  format.
*)
theory ProtocolAPI.

  (** Protocol library *)
  clone import ProtocolLibrary.

  (** Secret variables *)
  type svar_t.

  (** API calls *)
  (** 
    An API call can be either a call to the declassify protocol,
    to an I/O operation to a secret operator protocol.
  *)
  type apiCall_data = [
    | Call_declass of svar_t
    | Call_in of svar_t
    | Call_out of svar_t
    | Call_sop of sop_t & svar_t & value_t list & svar_t list
  ].

  (** API response *)
  (** 
    The API can generate responses to the declassify protocol,
    to an I/O operation to a secret operator protocol.
  *)
  type apiRes_data = value_t.

  (** API interaction buffer *)
  (**
    The buffer used to interact with the API can be filled 
    either with an API call or with an API response
  *)
  type apiCallRes = [
    | ApiCall of apiCall_data
    | ApiRes of apiRes_data
  ].

  (** Extracts an API call from the buffer *)
  op apiCall (x: apiCallRes) : apiCall_data option =
    with x = ApiCall y => Some y
    with x = ApiRes y => None.

  (** Extracts an API response from the buffer *)
  op apiRes (x: apiCallRes) : apiRes_data option =
    with x = ApiCall y => None
    with x = ApiRes y => Some y.

  (** API realisation *)
  clone import API with 
    type public_t = value_t,
    type inputs_t = inputs_t,
    type outputs_t = outputs_t,
    type svar_t = svar_t,
    type sop_t = sop_t,
    type sideInfo_t = sideInfo_t,
    type apiCall_data = apiCall_data,
    type apiRes_data = apiRes_data,
    type apiCallRes = apiCallRes,
    op apiCall = apiCall,
    op apiRes = apiRes.

end ProtocolAPI.

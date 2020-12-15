(** Abstract class for secret sharing schemes *)
require import List.

(** 
  A secret sharing scheme is a cryptographic primitive whose
  goal is to "split" some value into _n_ shares, such that the
  knowledge of _t_ shares (_t_ < _n_) does not reveal any
  sensitive information about the original value that was
  shared.
*)
theory SecretSharingScheme.

  (** Party identifier *)
  type partyId_t. (* 0..n_parties-1 *)

  (** Number of parties *)
  op n : int.
  (** Threshold of corrupt parties *)
  op t : int.

  (** Values *)
  type value_t.
  (** Individual shares *)
  type share_t.
  (** Set of all shares *)
  type sharedValue_t = share_t list.

  (** Shares a value among n-shares *)
  op [lossless] nshr : int -> value_t -> sharedValue_t distr.
  (** Unshares a shared value *)
  op unshr: sharedValue_t -> value_t.

end SecretSharingScheme.

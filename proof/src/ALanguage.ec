(** Abstract class for programming languages *)
require import AllCore List.

(** 
  Our language abstraction does not impose any restriction
  on the programs it tolerates, as languages are abstracted
  via a single type [L].

  Nevertheless, our language class admits the possibility of
  languages tolerating public and secret values and, consequently,
  public and secret operators.
*)
theory Language.

  (** Language *)
  type L.

  (** Public values *)
  type public_t.
  (** Secret values *)
  type secret_t.

  (** Secret operators *)
  type sop_t.

  (** Input format *)
  type inputs_t.

  (** Output format *)
  type outputs_t.

end Language.


require import AAPI ALanguage AMPSemantics MPAPISemantics AProtocolLibrary ProtocolAPI.
require import MPCProtocolLibrary ASecretSharingScheme.

type partyId_t = [ | P1 | P2 | P3 ].

clone import SecretSharingScheme as SS with
  type partyId_t = partyId_t,
  op n = 3,
  op t = 1.

clone import MPCProtocolLibrary as MPCLib with
  type SecretSharingScheme.partyId_t = partyId_t,
  op SecretSharingScheme.n = 3,
  op SecretSharingScheme.t = 1,
  type SecretSharingScheme.value_t = value_t,
  type SecretSharingScheme.share_t = share_t,
  op SecretSharingScheme.nshr = nshr,
  op SecretSharingScheme.unshr = unshr.

clone import ProtocolAPI as MPCAPI with
  op ProtocolLibrary.n = MPCProtocolLibrary.n,
  type ProtocolLibrary.partyId_t = partyId_t,
  type ProtocolLibrary.value_t = value_t,
  type ProtocolLibrary.inputs_t = inputs_t,
  type ProtocolLibrary.outputs_t = outputs_t,
  type ProtocolLibrary.msg_data = msg_data,
  type ProtocolLibrary.leakage_t = leakage_t,
  type ProtocolLibrary.sideInfo_t = sideInfo_t,
  type ProtocolLibrary.sop_t = sop_t,
  op ProtocolLibrary.sop_spec = sop_spec,
  op ProtocolLibrary.prot_declass = prot_declass,
  op ProtocolLibrary.prot_in = prot_in,
  op ProtocolLibrary.prot_out = prot_out,
  op ProtocolLibrary.prot_sop = prot_sop,
  op ProtocolLibrary.sim_declass = sim_declass,
  op ProtocolLibrary.sim_in = sim_in,
  op ProtocolLibrary.sim_out = sim_out,
  op ProtocolLibrary.sim_sop = sim_sop.

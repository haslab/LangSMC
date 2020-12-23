require import AllCore List SmtMap Distr FSet.

(**

  This is a simplified version of the formalisation the
  "Language-based Secure Multiparty Computation", used
  for illustration purposes in the companion article
  "A Formal Treatment of the Role of Verified Compilers in Secure
  Computation" (Journal of Logical and Algebraic Methods in
  Programming, ...).
  We structured this file by following the paper organization.
  It includes definitions and theorem statements, but proofs have
  been omitted -- instead, we add pointers to the corresponding
  statements/proofs in the original development.

  Remark: some types, such as 'S' and 'SideInfo', have been
 presented in the paper as abstract, for the sake of simplification.
 However, in order to provide definitions not included in the paper,
 we had to refine them is this file.
*)

(**
 Section 2 - Programming languages and semantics
 ===============================================
*)


(**
 2.1. Programming Language
*)

(* Semantic domain of values *)
type V.

(* Secret Operations *)
type sop_t.

(** Variables and security API call data  *)
type var_t.

(* Operation, public args, secret args handlers, secret result handler *)
type callData = sop_t*V list*V list*V option.


(* Abstract Language *)
theory Lang.
 type L, lconf_t.
 op initial_lconf: L -> lconf_t.
 op lstep: lconf_t -> lconf_t option.
 op lcallSt: lconf_t -> callData option.
 op lcallRet: V -> lconf_t -> lconf_t.
 (* remark: absent from the paper, as it is not used there... *)
 op lstep_iter (k:int) (st:lconf_t): lconf_t option =
   iter k (obind lstep) (Some st).
 axiom block_on_calls sigma:
   lcallSt sigma <> None => lstep sigma = None.
end Lang.

(* secret-sharing scheme *)
theory SecretSharing.
op n: int.		(* Number of parties *)
type S = V list.	(* shared values *)
op [lossless] share: V -> S distr.
op unshare: S -> V.
axiom ss_size v s: s \in share v => size s = n.
axiom ss_correct v: dmap (share v) unshare = dunit v.
end SecretSharing.


(**
 2.2. Computation over secret data
*)

theory API.

op n_parties, corrupted_parties: int.
axiom corrupted_subset: 0 < corrupted_parties < n_parties.

clone import SecretSharing with op n <- n_parties.


(* corrupted shares - wlog, we assume the first
  'corrupted_parties' to be corrupt *)
op C (x:S) : S = take corrupted_parties x.


(* SideInfo *)
type other_leak_t, trace_t.
type leak_t = [ leakCShares of S 
              | leakOther of other_leak_t ].
op leakCshrs (x: leak_t) : S option = 
 with x = leakCShares s => Some s
 with x = leakOther l => None.

type SideInfo =
 [ epsilon
 | leak of leak_t
 | trace of trace_t
 ].
op leakage (x: SideInfo): leak_t option =
 with x = epsilon => None
 with x = leak l => Some l
 with x = trace t => None.

op ctrace (x: SideInfo): trace_t option =
 with x = epsilon => None
 with x = leak l => None
 with x = trace t => Some t.

op leakedCshrs (x: SideInfo): S option =
 obind leakCshrs (leakage x).



(* Security API interface *)
module type API_t = {
  proc init(): unit
  proc eval_sop(o: sop_t, pargs: V list, 
                sargs: V list, sres: V option): (V*SideInfo) option
  proc set_input(x: S): bool 
  proc get_output(): S option
}.


(* sop arity *)
op sop_ar (o: sop_t): (int*int*bool).

(* input and output operations *)
op sop_input: sop_t.
op sop_output: sop_t.
axiom arity_input: sop_ar sop_input = (0,0,true).
axiom arity_output: sop_ar sop_output = (0,1,false).

(* checks arity *)
op sop_ar_check (o: sop_t, pargs: V list, sargs: V list, sres: V option): bool =
  sop_ar o = (size pargs, size sargs, sres <> None).

(* lsop specifications *)
op Fsop: sop_t -> V list * V list -> V * leak_t.
op pubres: sop_t -> leak_t -> V. 
(* lsop protocols *)
op [lossless] pi_sop
 : sop_t -> V list * S list -> (S * trace_t) distr.
op leakXtr: sop_t -> trace_t -> leak_t. (* leakage extractor *)
(* input and output protocols *)
op [lossless] pi_input: S -> trace_t distr.
op [lossless] pi_output: S -> (S * trace_t) distr.



(* lifting of env ops. *)
op env_getlist ['a, 'b] (m: ('a, 'b) fmap) (l: 'a list)
 : ('b list) option =
 foldr (fun ov or=>obind (fun v=>(omap ((::) v) or)) ov)
       (Some []) (map (("_.[_]") m) l).

op env_oupd ['a] (m: (V, 'a) fmap) (ov: V option) (x: 'a)
 : (V,'a) fmap =
 if ov = None then m else m.[oget ov <- x].

(* Ideal security library (Fig. 3) *)
module Alpha: API_t = {
  var senv: (V, V) fmap
  var ibuf: S option
  var obuf: S option
  proc init(): unit = {
    senv <- empty;
    ibuf <- None;
    obuf <- None;
  }
  proc eval_sop(o: sop_t, pargs: V list,
                sargs: V list, sres: V option): (V*SideInfo) option = {
    var v, vs, v', r, vsargs, l;
    if (sop_ar_check o pargs sargs sres) {
      if (o = sop_input && ibuf <> None) {
        v <- unshare (oget ibuf);
        senv <- senv.[ oget sres <- v ];
        r <- Some (witness, leak (leakCShares (C vs)));
        ibuf <- None;
      } else {
        if (o = sop_output && obuf = None) {
          v <- oget senv.[head witness sargs];
          vs <$ share v;
          obuf <- Some vs;
          r <- Some (witness, leak (leakCShares (C vs)));
        } else {
          vsargs <- oget (env_getlist senv sargs);
          (v', l) <- Fsop o (pargs,vsargs);
          r <- Some (v', leak l);
        }
      }
    } else {
        r <- None;
    } 
    return r;
  }
  proc set_input(x: S): bool = {
    var r;
    if (ibuf = None) {
      ibuf <- Some x;
      r <- true;
    } else {
      r <- false;
    }
    return r;
  }
  proc get_output(): S option = {
    var r;
    r <- obuf;
    obuf <- None;
    return r;
  }
}.

(* Real security library (Fig. 4) *)
module Beta: API_t = {
  var senv: (V, S) fmap
  var ibuf: S option
  var obuf: S option
  proc init(): unit = {
    senv <- empty;
    ibuf <- None;
    obuf <- None;
  }
  proc eval_sop(o: sop_t, pargs: V list, sargs: V list, sres: V option): (V*SideInfo) option = { 
    var vs, r, t, svsargs, svs, v;
    if (sop_ar_check o pargs sargs sres) {
      if (o = sop_input && ibuf <> None) {
        vs <- oget ibuf;
        senv <- senv.[ oget sres <- vs ];
        ibuf <- None;
        t <$ pi_input vs;
        r <- Some (witness, trace t);
      } else {
        if (o = sop_output && obuf = None) {
          vs <- oget senv.[head witness sargs];
          (svs, t) <$ pi_output vs;
          obuf <- Some vs;
          r <- Some (witness, trace t);
        } else {
          svsargs <- oget (env_getlist senv sargs);
          (svs, t) <$ pi_sop o (pargs, svsargs);
          v <- pubres o (leakXtr o t);
          r <- Some (v, trace t);
        }
      }
    } else {
        r <- None;
    } 
    return r;
  }
  proc set_input(x: S): bool = {
    var r;
    if (ibuf = None) {
      ibuf <- Some x;
      r <- true;
    } else {
      r <- false;
    }
    return r;
  }
  proc get_output(): S option = {
    var r;
    r <- obuf;
    obuf <- None;
    return r;
  }
}.

end API.

(**
 2.3. Ideal- and Real-world semantics
*)

(* Single Language setting *)
theory SingleLanguage.

clone import Lang as L.

op n_parties, corrupted_parties: int.
axiom corrupted_subset: 0 < corrupted_parties < n_parties.

clone import API
 with op n_parties <- n_parties,
      op corrupted_parties <- corrupted_parties
      proof corrupted_subset by apply corrupted_subset.

import API.SecretSharing.


(* Ideal-world Language Semantics *)
module type IdealSem_t = {
  proc init(P: L): unit
  proc step(): SideInfo option
}.

module IdealSem : IdealSem_t = {
  var st: lconf_t
  proc init(P: L): unit = {
    st <- initial_lconf P;
  }
  proc step(): SideInfo option = {
    var cst, info, oc, o, pargs, sargs, sres, vp, l, oeval;
    cst <- lcallSt st;
    info <- None;
    if (cst <> None) {
      (o, pargs, sargs, sres) <- oget cst;
      oeval <@ Alpha.eval_sop(o,pargs,sargs,sres);
      if (oeval <> None) {
        (vp,l) <- oget oeval;
        st <- lcallRet vp st;
        info <- Some l;
      }
    } else {
        oc <- lstep st;
        if (oc <> None)
        st <- oget oc;
        info <- Some epsilon;
    }
    return info;
  }
}.


(* Real-world Language Semantics *)
module type RealSem_t = {
  proc init(P: L): unit
  proc stepP(i: int): bool
  proc stepS(): SideInfo option
}. 

type gconf_t = (int, lconf_t) fmap.

(* extract all call-states from a global conf. *)
op allCallSts (st: gconf_t) : callData option list =
 map (fun i => lcallSt (oget (st.[i]))) (iota_ 1 n_parties).

(* synchronization points:
     - check if all confs have the same [apiCall_data] info              *)
op allEqSome ['a] (l: 'a option list): 'a option =
 with l = "[]" => None
 with l = (::) x xs => if all (fun y => x=y) xs
                       then x
                       else None.

(** callState of a global conf. *)
op gcallSt (gst: gconf_t): callData option =
 allEqSome (allCallSts gst).

(* predicate to check if a global conf. is at a sync. point *)
op sync (gst: gconf_t): bool = gcallSt gst <> None.

(** updates result in a global state *)
op gcallRet (v: V) (st: gconf_t): gconf_t =
 foldr (fun i m => m.[i <- lcallRet v (oget m.[i])]) empty (iota_ 1 n_parties).

module RealSem: RealSem_t = {
  var sigma: (int, lconf_t) fmap
  proc init(P: L): unit = {
    sigma <- foldr (fun i x => x.[i <- initial_lconf (P)]) empty (iota_ 1 n_parties);
  }
  proc stepP(i: int): bool = {
    var oc, r;
    r <- false;
    oc <- lstep (oget sigma.[i]);
    if (0 < i <= n_parties && oc <> None) {
      sigma <- sigma.[i <- oget oc];
      r <- true;
    }
    return r;
  }
  proc stepS(): SideInfo option = {
    var cst, info, o, pargs, sargs, sres, oeval, vp, tau;
    cst <- gcallSt sigma;
    info <- None;
    if (cst <> None) {
      (o, pargs, sargs, sres) <- oget cst;
      oeval <@ Beta.eval_sop(o,pargs,sargs,sres);
      if (oeval <> None) {
        (vp,tau) <- oget oeval;
        sigma <- gcallRet vp sigma;
        info <- Some tau;
      }
    }
    return info;
  }
}.

(* Remark: Multi-language real-world semantics presented bellow... *)


(**
 Section 3 - Program-based secure computation
 ============================================
*)

(**
 3.1. Security Model
*)

(** Adversarial interface *)

(* Environment *)
module type Z_IO_t = {
  proc set_input(x: S): bool
  proc get_output(): S option
}.
type any.
module type Z_Adv_t = {
  proc activate(): any
}.
module type Z_t(Z_IO: Z_IO_t, Z_Adv: Z_Adv_t) = {
  proc run(): bool
}.

(* Attacker *)
module type Adv_Sem_t = {
  proc stepP(i: int): bool
  proc stepS(): SideInfo option
}.
module type Adv_t(Sem: Adv_Sem_t) = {
  proc init(P:L): unit
  proc activate(): any
}.

(* Simulator *)
module type Sim_Sem_t = {
  proc step(): SideInfo option
}.
module type Sim_t(Sem: Sim_Sem_t) = { 
  proc init(P:L): unit
  proc activate(): any
}.


(** Ideal- and Real-world definitions *)
module IDEAL(Z: Z_t, A: Sim_t) = {
  module Adv = A(IdealSem)
  proc game(P: L): bool = {
    var b;
    Alpha.init();
    IdealSem.init(P);
    Adv.init(P);
    b <@ Z(Alpha, Adv).run();
    return b;
  }
}.

module REAL(Z: Z_t, A: Adv_t) = {
  module Adv = A(RealSem)
  proc game(P: L): bool = {
    var b;
    Beta.init();
    RealSem.init(P);
    Adv.init(P);
    b <@ Z(Alpha, Adv).run();
    return b;
  }
}.

(**
 4. Vertical dimension: single-program secure computation
 ========================================================
*)

(**
 4.1. API security
*)

(* strong simulators *)
op [lossless] sim_output: S * S -> trace_t distr.
(* weak simulators *)
op [lossless] sim_input: S -> trace_t distr.
op [lossless] sim_sop: sop_t -> V list * S list * leak_t -> (S * trace_t) distr.
 
(* Simulator experiments (Fig. 6) *)
module SimExp = {
  proc outputSimL(vsarg: S): V * S * trace_t = {
    var vout, vsout, t;
    vout <- unshare vsarg;
    vsout <$ share vout;
    t <$ sim_output (vsarg, vsout);
    return (vout, C vsout, t);
  }
  proc outputSimR(vsarg: S): V * S * trace_t = {
    var vsout, t;
    (vsout, t) <$ pi_output vsarg;
   return (unshare vsout, C vsout, t);
  }
  proc inputSimL(vsin: S): trace_t = {
    var t;
    t <$ sim_input (C vsin);
    return t;
  }
  proc inputSimR(vsin: S): trace_t = {
    var t;
    t <$ pi_input vsin;
    return t;    
  }
  proc sopSimL(o: sop_t, vpargs: V list, vsargs: S list)
              : V * S * leak_t * trace_t = {
    var sv, l, svs, t;
    (sv, l) <- Fsop o (vpargs, map unshare vsargs);
    (svs,t) <$ sim_sop o (vpargs, map C vsargs, l);
    return (sv, svs, l, t);
  }
  proc sopSimR(o: sop_t, vpargs: V list, vsargs: S list)
              : V * S * leak_t * trace_t = {
    var svs, t;
    (svs, t) <$ pi_sop o (vpargs, vsargs);
    return (unshare svs, C svs, leakXtr o t, t);
  }
}.

(* Security assumptions (Def. 2) *)
axiom APIsec_output:
 equiv [ SimExp.outputSimL ~ SimExp.outputSimR
       :  ={vsarg} ==> ={res}
       ].
axiom APIsec_input:
 equiv [ SimExp.inputSimL ~ SimExp.inputSimR
       :  ={vsin} ==> ={res}
       ].
axiom APIsec_sop:
 equiv [ SimExp.sopSimL ~ SimExp.sopSimR
       :  ={o,vpargs,vsargs} ==> ={res}
       ].


(** Simulated library (corrupted-shares) - Fig. 7 *)
module Gamma = {
  var senv : (V, S) fmap
  proc init(): unit = {
    senv <- empty;
  }
  proc sim_sop( o: sop_t, pargs: V list, sargs: V list
              , sres: V option, l: SideInfo)
      : (V*SideInfo) option = {
    var vs, r, t, svsargs, svs, v;
    if (sop_ar_check o pargs sargs sres) {
      if (o = sop_input) {
        vs <- oget (leakedCshrs l);
        senv <- senv.[ oget sres <- vs ];
        t <$ sim_input vs;
        r <- Some (witness, trace t);
      } else {
        if (o = sop_output) {
          vs <- oget senv.[head witness sargs];
          svs <- oget (leakedCshrs l);
          t <$ sim_output (vs,svs);
          r <- Some (witness, trace t);
        } else {
          svsargs <- oget (env_getlist senv sargs);
          (svs, t) <$ sim_sop o (pargs, svsargs, oget (leakage l));
          senv <- env_oupd senv sres svs;
          v <- pubres o (leakXtr o t);
          r <- Some (v, trace t);
        }
      }
    } else {
        r <- None;
    } 
    return r;
  }
}.

(**
 4.2. Security Theorem
*)

(** Simulator *)
module SimulatedRealSem = {
  var sigma: (int, lconf_t) fmap
  proc init(P: L): unit = {
    sigma <- foldr (fun i x => x.[i <- initial_lconf (P)]) empty (iota_ 1 n_parties);
  }
  proc stepP(i: int): bool = {
    var oc, r;
    r <- false;
    oc <- lstep (oget sigma.[i]);
    if (0 < i <= n_parties && oc <> None) {
      sigma <- sigma.[i <- oget oc];
      r <- true;
    }
    return r;
  }
  proc stepS(l: SideInfo): SideInfo option = {
    var cst, info, o, pargs, sargs, sres, oeval, vp, tau;
    cst <- gcallSt sigma;
    info <- None;
    if (cst <> None) {
      (o, pargs, sargs, sres) <- oget cst;
      oeval <@ Gamma.sim_sop(o,pargs,sargs,sres,l);
      if (oeval <> None) {
        (vp,tau) <- oget oeval;
        sigma <- gcallRet vp sigma;
        info <- Some tau;
      }
    }
    return info;
  }
}.

module SimSem(ISem: Sim_Sem_t): Adv_Sem_t = {
  proc stepP(i: int): bool = {
    var b;
    if (i = 1) { ISem.step(); }
    b <@ SimulatedRealSem.stepP(i);
    return b;
  }
  proc stepS(): SideInfo option = {
    var tau;
    tau <- None;
    if (sync(SimulatedRealSem.sigma)) {
      tau <@ ISem.step();
      tau <@ SimulatedRealSem.stepS(oget tau);
    }
    return tau;
  }
}.

module Sim(A: Adv_t, ISem: Sim_Sem_t) = {
  proc init = A(SimSem(ISem)).init
  proc activate = A(SimSem(ISem)).activate
}.


(** THEOREM 1 *)
equiv Thm1 (Z <: Z_t)(A <: Adv_t):
 REAL(Z, A).game ~ IDEAL(Z, Sim(A)).game
 : ={P} ==> ={res}.
proof.
(* The proof of this theorem can be found on file
'Vertical.ec' (theorem 'Security'). *)
admitted.


(**
 5. Horizontal dimension: Multi-program secure computation
 =========================================================
*)


(** Simulated library (public-values only) *)
module Lambda = {
  proc init(): unit = { }
  proc sim_sop( o: sop_t, pargs: V list, sargs: V list
              , sres: V option, l: SideInfo)
      : (V*SideInfo) option = {
    var r;
    if (sop_ar_check o pargs sargs sres) {
      r <- Some (pubres o (oget (leakage l)), l);
    } else {
        r <- None;
    } 
    return r;
  }
}.

(* Simulated ideal-world semantics *)
module SimIdealSem = {
  var st: lconf_t
  proc init(P: L): unit = {
    st <- initial_lconf P;
  }
  proc step(ll: SideInfo): SideInfo option = {
    var cst, info, oc, o, pargs, sargs, sres, vp, l, oeval;
    cst <- lcallSt st;
    info <- None;
    if (cst <> None) {
      (o, pargs, sargs, sres) <- oget cst;
      oeval <@ Lambda.sim_sop(o,pargs,sargs,sres,ll);
      if (oeval <> None) {
        (vp,l) <- oget oeval;
        st <- lcallRet vp st;
        info <- Some ll;
      }
    } else {
        oc <- lstep st;
        if (oc <> None)
        st <- oget oc;
        info <- Some epsilon;
    }
    return info;
  }
}.

end SingleLanguage.

(**
 5.2. Program-based small-step simulation
*)

theory CertifiedCompiler.

(* source language *)
clone import Lang as LS.
(* target language *)
clone Lang as LT.
(* compiler *)
op comp : L -> LT.L.
(* relation ≈ *)
op relLSt : lconf_t -> LT.lconf_t -> bool.
(* Certified-compiler assumptions *)
axiom relLSt_init (P:LS.L):
 relLSt (LS.initial_lconf P) (LT.initial_lconf (comp P)).
axiom backwardsim ss st kt st':
 relLSt ss st =>
 LT.lstep_iter kt st = Some st' =>
 LT.lcallSt st' <> None =>
 (exists ks ss', LS.lstep_iter ks ss = Some ss'
                 /\ relLSt ss' st'
                 /\ 0 <= ks).
end CertifiedCompiler.

(**
 5.3. Ideal certified compilation
*)

theory IdealCompilation.

(* source language *)
clone Lang as LS.
clone SingleLanguage as SLS
 with theory L <- LS.

import SLS.API SLS.API.SecretSharing.

(* target language *)
clone Lang as LT.
clone SingleLanguage as SLT
 with theory L <- LT,
      type API.other_leak_t <- other_leak_t,
      type API.trace_t <- trace_t,
      type API.SideInfo <- SideInfo,
      type any <- SLS.any.

(* certified compiler assumption *)
clone CertifiedCompiler as Comp
 with theory LS <- LS,
      theory LT <- LT.

(* [sync] predicate - checks if lconf is at a sync. point *)
op syncS (st: LS.lconf_t) : bool = LS.lcallSt st <> None.
op syncT (st: LT.lconf_t) : bool = LT.lcallSt st <> None.
 
(* Ideal target semantics simulator (D) - Fig. 8 *)
module DSem(ISem: SLS.Sim_Sem_t): SLT.Sim_Sem_t = {
  proc init(P:LS.L): unit = { 
    SLS.SimIdealSem.init(P);
    SLT.SimIdealSem.init(Comp.comp(P));
  }
  proc step(): SideInfo option = {
    var tau;
    if (! syncT SLT.SimIdealSem.st) {
      tau <@ SLT.SimIdealSem.step(epsilon);
    } else {
      while (!syncS SLS.SimIdealSem.st) {
        SLS.SimIdealSem.step(epsilon);
        tau <@ ISem.step();
      }
      tau <@ ISem.step();
      if (tau <> None) {
        SLT.SimIdealSem.step(oget tau);
        SLS.SimIdealSem.step(oget tau);
      }
    }
    return tau;
  }
}.
module D(A: SLT.Sim_t, ISem: SLS.Sim_Sem_t) = {
  proc init(P: LS.L): unit = {
    DSem(ISem).init(P);
  }
  proc activate = A(DSem(ISem)).activate
}.

(** Theorem 2 *)
equiv Thm2 (Z <: SLT.Z_t)(A <: SLT.Sim_t):
 SLT.IDEAL(Z, A).game ~ SLS.IDEAL(Z, D(A)).game
 : P{1}=Comp.comp P{2} ==> ={res}.
proof.
(* This "arrow" of the diagram from Fig. 1 has not been included in
 the formalisation.
 However, its proof strategy is essentially that of theorem Thm3
 presented below.
 *)
admitted.

end IdealCompilation.

(**
 5.4. Real certified compilation
*)

theory MultiLanguage.
(* remark: we instantiate the multi-language setting
 with 3 parties (1 corrupted) *)

(* source language *)
clone import SingleLanguage as LS
 with op n_parties <- 3,
      op corrupted_parties <- 1
      proof corrupted_subset by done.

import LS.API LS.API.SecretSharing.


(* target languages *) 
clone Lang as L1.
clone CertifiedCompiler as C1
 with theory LS <- LS.L,
      theory LT <- L1.
clone Lang as L2.
clone CertifiedCompiler as C2
 with theory LS <- LS.L,
      theory LT <- L2.
clone Lang as L3.
clone CertifiedCompiler as C3
 with theory LS <- LS.L,
      theory LT <- L3.

(* checks of global conf. is at a sync. point *)
op sync (st:L1.lconf_t*L2.lconf_t*L3.lconf_t): bool =
  L1.lcallSt st.`1 <> None
  && L1.lcallSt st.`1 = L2.lcallSt st.`2
  && L1.lcallSt st.`1 = L3.lcallSt st.`3.

(* Real-world semantics (multi-language) *)
module RealSemML = {
  var sigma: L1.lconf_t * L2.lconf_t * L3.lconf_t
  proc init(P1: L1.L, P2: L2.L, P3: L3.L): unit = {
    sigma <- (L1.initial_lconf P1,
              L2.initial_lconf P2,
              L3.initial_lconf P3);
  }
  proc stepP(i: int): bool = {
    var oc1, oc2, oc3, r;
    r <- false;
    if ( i = 1 ) {
      oc1 <- L1.lstep sigma.`1;
      if (oc1 <> None) {
        sigma <- (oget oc1, sigma.`2, sigma.`3);
        r <- true;
      }
    }
    if ( i = 2 ) {
      oc2 <- L2.lstep sigma.`2;
      if (oc2 <> None) {
        sigma <- (sigma.`1, oget oc2, sigma.`3);
        r <- true;
      }
    }
    if ( i = 3 ) {
      oc3 <- L3.lstep sigma.`3;
      if (oc3 <> None) {
        sigma <- (sigma.`1, sigma.`2, oget oc3);
        r <- true;
      }
    }
    return r;
  }
  proc stepS(): SideInfo option = {
    var cst, info, o, pargs, sargs, sres, oeval, vp, tau;
    cst <- if (sync sigma) then L1.lcallSt sigma.`1 else None;
    info <- None;
    if ( cst <> None ) {
      (o, pargs, sargs, sres) <- oget cst;
      oeval <@ Beta.eval_sop(o,pargs,sargs,sres);
      if (oeval <> None) {
        (vp,tau) <- oget oeval;
        sigma <- (L1.lcallRet vp sigma.`1,
                  L2.lcallRet vp sigma.`2,
                  L3.lcallRet vp sigma.`3);
        info <- Some tau;
      }
    }
    return info;
  }
}.

(* multi-language 'REAL' security experiment *)
module REAL_ML(Z: Z_t, A: Adv_t) = {
  module Adv = A(RealSem)
  proc game(P: LS.L.L): bool = {
    var b;
    Beta.init();
    RealSemML.init(C1.comp P,C2.comp P,C3.comp P);
    Adv.init(P);
    b <@ Z(Alpha, Adv).run();
    return b;
  }
}.

(* Simulated (multi-language) real-world semantics *)
module SimRealSemML = {
  var sigma: L1.lconf_t * L2.lconf_t * L3.lconf_t
  proc init(P1: L1.L, P2: L2.L, P3: L3.L): unit = {
    sigma <- (L1.initial_lconf P1,
              L2.initial_lconf P2,
              L3.initial_lconf P3);
  }
  proc stepP(i: int): bool = {
    var oc1, oc2, oc3, r;
    r <- false;
    if ( i = 1 ) {
      oc1 <- L1.lstep sigma.`1;
      if (oc1 <> None) {
        sigma <- (oget oc1, sigma.`2, sigma.`3);
        r <- true;
      }
    }
    if ( i = 2 ) {
      oc2 <- L2.lstep sigma.`2;
      if (oc2 <> None) {
        sigma <- (sigma.`1, oget oc2, sigma.`3);
        r <- true;
      }
    }
    if ( i = 3 ) {
      oc3 <- L3.lstep sigma.`3;
      if (oc3 <> None) {
        sigma <- (sigma.`1, sigma.`2, oget oc3);
        r <- true;
      }
    }
    return r;
  }
  proc stepS(t: SideInfo): SideInfo option = {
    var cst, info, o, pargs, sargs, sres, oeval, vp, tau;
    cst <- if (sync sigma) then L1.lcallSt sigma.`1 else None;
    info <- None;
    if ( cst <> None ) {
      (o, pargs, sargs, sres) <- oget cst;
      oeval <@ Lambda.sim_sop(o,pargs,sargs,sres,leak (leakXtr o
  (oget (ctrace t))));
      if (oeval <> None) {
        (vp,tau) <- oget oeval;
        sigma <- (L1.lcallRet vp sigma.`1,
                  L2.lcallRet vp sigma.`2,
                  L3.lcallRet vp sigma.`3);
        info <- Some tau;
      }
    }
    return info;
  }
}.

(* simulator (D) - Fig. 9 *)
module DSem(RSem: LS.Adv_Sem_t): LS.Adv_Sem_t = {
  proc init(P:LS.L.L): unit = { 
    SimRealSemML.init(C1.comp P, C2.comp P, C3.comp P);
  }
  proc stepP(i: int): bool = {
    var b;
    b <@ SimRealSemML.stepP(i);
    return b;
  }
  proc stepS(): SideInfo option = {
    var tau, b;
    tau <- None;
    if ( sync SimRealSemML.sigma ) {
      b <- true;
      while (b) { b <@ RSem.stepP(1); }
      b <- true;
      while (b) { b <@ RSem.stepP(2); }
      b <- true;
      while (b) { b <@ RSem.stepP(3); }
      tau <@ RSem.stepS();
      SimRealSemML.stepS(oget tau);
    }
    return tau;
  }
}.
module D(A: LS.Adv_t, RSem: LS.Adv_Sem_t) = {
  proc init(P: LS.L.L): unit = {
    DSem(RSem).init(P);
  }
  proc activate = A(DSem(RSem)).activate
}.

(** Theorem 3 *)
equiv Thm3 (Z <: LS.Z_t)(A <: LS.Adv_t):
 REAL_ML(Z, A).game ~ LS.REAL(Z, D(A)).game
 : ={P} ==> ={res}.
proof.
(* The proof can be found at file 'Horizontal.ec'
 (theorem 'SecurityMT')  *)
admitted.

end MultiLanguage.


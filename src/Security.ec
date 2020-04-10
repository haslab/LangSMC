require import AllCore List SmtMap Distr IntExtra IntDiv DMap FSet.

require import ALanguage ASecretSharingScheme AProtocolLibrary AAPI ASPSemantics AMPSemantics.
require import MPCProtocolLibrary ProtocolAPI SPAPISemantics MPAPISemantics.
require import MPProtocolAPISemantics.

theory Security.

clone import Language.

clone import MultiPartyProtocolAPISemantics with
 type L1.L = L,
 type L2.L = L,
 type L3.L = L.
import ProtocolAPI.
import ProtocolLibrary.
import SecretSharingScheme.
import MultiPartyAPISemantics.

clone import SinglePartyAPISemantics as IdealSemantics with
theory Language <- L1,
type API.public_t = value_t,
type API.inputs_t = sharedValue_t,
type API.outputs_t = sharedValue_t,
type API.svar_t = svar_t,
type API.sop_t = sop_t,
type API.sideInfo_t = MPCProtocolLibrary.sideInfo_t,
type API.apiCall_data = apiCall_data,
type API.apiRes_data = apiRes_data,
type API.apiCallRes = apiCallRes,
op API.apiCall = apiCall,
op API.apiRes = apiRes,
op updRes (x: apiRes_data option) (st: ('a,'b) APIst) = (omap ApiRes x, st.`2),
op st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, (x.`2.`1, x.`2.`2)),
type EnvL = SemP1.EnvL,
op stepL = SemP1.stepL,
op initStateL = SemP1.initStateL,
type SinglePartySemantics.output_event_t = MultiPartySemantics.output_event_t.

module IdealFunctionality (API : IdealSemantics.API.API_t) = {

   var st : configuration_t

   proc init(P : L) : unit = {
     st <- initial_configuration P;
     API.init();
   }
   proc step() : sideInfo_t option = {
     var r, lst, newst, cst;
     var v, xx, si;
     var vsio, asio, xxsio;

     lst <- sigma st;
     r <- None;
     cst <- callSt lst;

     if (cst = None) {
       newst <- stepL (progSt lst) (envSt lst) (resSt lst);
       if (newst <> None) {
         st <- upd_sigma (oget newst) st;
       }
     }
     else {
       match (oget cst) with
       | Call_declass a => { vsio <@ API.declass(a); 
                              if (vsio <> None) {
                                (v, si) <- oget vsio;
                                st <- upd_SigmaAPI (Some v) st; 
                                r <- Some si; 
                              }
                            }
       | Call_in a => { if (ib st <> None) {
                        asio <@ API.input(a, oget (ib st)); 
                        if (asio <> None) {
                          si <- oget asio;
                          st <- upd_ib None st;
                          st <- upd_SigmaAPI None st; 
                          r <- Some si; 
                        } 
                      }
                     }
       | Call_out sv => { if (ob st = None) {
                           xxsio <@ API.output(sv);
                           if (xxsio <> None) {
                             (xx, si) <- oget xxsio;
                             st <- upd_ob (Some xx) st;
                             st <- upd_SigmaAPI None st; 
                             r <- Some si; } } }
       | Call_sop sop a pargs sargs => { asio <@ API.sop(sop, pargs, sargs, a);
                                       if (asio <> None) {
                                         si <- oget asio;
                                         st <- upd_SigmaAPI None st;
                                         r <- Some si; } }
       end;
     }

     return r;
   }
   proc setInput(x: inputs_t): bool = {
     var r <- false;
     if (ib st = None) {
       r <- true;
       st <- upd_ib (Some x) st;
     }
     return r;
   }
   proc getOutput(): outputs_t option = {
     var r: outputs_t option;
     r <- ob st;
     if (r <> None) {
       st <- upd_ob None st;
     }
     return r;
   }
 }.

import SecretSharingScheme.
import MPCProtocolLibrary.

module API_Ideal : IdealSemantics.API.API_t = {
  var senv: (svar_t, value_t) fmap
  proc init(): unit = {
    senv <- empty;
  }
  proc nparties(): int = { return 1; }
  (* [declass] leaks the declassified value *)
  proc declass(a: svar_t): (value_t * sideInfo_t) option = {
    var v, r;
    r <- None;
    if (a \in senv) { v <- oget senv.[a]; r <- Some (v, Leak v); }
    return r;
  }
  (* [in] leaks the input shares from corrupted parties *)
  proc input(a : svar_t, inp: inputs_t): sideInfo_t option = {
    senv <- senv.[ a <- unshr(inp) ];
    return Some (CorruptedShares (take t inp));
  }
  (* [out] leaks the output shares from corrupted parties *)
  proc output(a: svar_t): (sharedValue_t * sideInfo_t) option = {
    var yy, r;
    r <- None;
    if (a \in senv) { 
      yy <$ nshr SecretSharingScheme.n (oget senv.[a]); 
      r <- Some (yy, CorruptedShares (take t yy)); 
    }
    return r;
  }
  proc sop(sop: sop_t, pargs: value_t list, sargs: svar_t list, a : svar_t) : sideInfo_t option = {
    var y, l, r;
     r <- None;
     if (forall x, x \in sargs /\ x \in senv) {
       (y, l) <- MPCProtocolLibrary.sop_spec sop pargs (map (fun x => (oget senv.[x])) sargs);
       senv <- senv.[ a <- y ];
       r <- Some {| leakage=l; trace=[]|};
     }
    return r;
  }
}.

(* REAL FUNCTIONALITY for arbritary sops:
  - [sargs] are now proper n-shared values
  - side information is the communication trace of corrupted parties *)

(* Concrete protocols. Return the communication traces for corrupted parties 
module type prot_t = {
proc prot_declass(a: sharedValue_t): value_t * trace_t
proc prot_in(inp: sharedValue_t): sharedValue_t * trace_t
proc prot_out(a: sharedValue_t): sharedValue_t * trace_t
proc prot_sop(sop: sop_t, pargs: value_t list, sargs: sharedValue_t list)
     : sharedValue_t * trace_t
}. *)

(* The REAL API *)
module API_Real : MultiPartyAPISemantics.API.API_t = {
var senv: (svar_t, sharedValue_t) fmap
proc init(): unit = {
  senv <- empty;
}
proc nparties(): int = { return SecretSharingScheme.n; }
proc declass(a: svar_t): (value_t * sideInfo_t) option = {
  var vtr, r;
   r <- None;
   if (a \in senv) {
    vtr <@ APIsec.prot_declass(oget senv.[a]);
     r <- Some vtr;
   }
  return r;
}
proc input(a : svar_t, inp: sharedValue_t): sideInfo_t option = {
  var tr;
   tr <@ APIsec.prot_in(inp);
  senv <- senv.[ a <- inp ];
  return Some tr;
}
proc output(a: svar_t): (sharedValue_t * sideInfo_t) option = {
  var o, tr, r;
   r <- None;
   if (a \in senv) {
     (o, tr) <@ APIsec.prot_out(oget (senv.[a]));
     r <- Some (o, tr);
   }
  return r;
}
proc sop(sop: sop_t, pargs: value_t list, sargs: svar_t list, a : svar_t) : sideInfo_t option = {
  var r, tr, y;
   r <- None;
   if (forall x, x \in sargs /\ x \in senv) {
     (y, tr) <@ APIsec.prot_sop(sop,pargs, map (fun x => oget senv.[x]) sargs);
     senv <- senv.[ a <- y ];
     r <- Some tr;
   }
  return r;
}
}.


module type IdealInterface = {
  proc init(P : L) : unit
  proc step(): sideInfo_t option
  (*proc stepOutput() : sharedValue_t * sideInfo_t option*)
}.

(*module type SimEnvInterface = {
 proc activate(): trace_t
}.*)

module type SimInterface (Sem: IdealInterface) = {
  include MultiPartySemantics.AdvSemInterface
}.

(*module API_Simulator (ISem : IdealInterface) = {
  var senv: (svar_t, sharedValue_t) fmap
  proc init(): unit = {
    senv <- empty;
  }
  proc declass(a: svar_t): (value_t * sideInfo_t) option = {
    var v, tr, l, r;
     r <- None;
     if (a \in senv) {
       l <@ ISem.step();
       (v,tr) <@ APIsec.sim_declass(oget (senv.[a]), oget (oget l).`leakage); 
       r <- Some (v, tr);
     }
    return r;
  }

  proc input(a : svar_t, inp: sharedValue_t): sideInfo_t option = {
    var tr, l, r;
    r <- None;
    l <@ ISem.step();
    tr <@ APIsec.sim_in(oget (oget l).`leakage);
    senv <- senv.[ a <- take t inp ];
    r <- Some tr;
    return r;
  }

  proc output(a: svar_t): sideInfo_t option = {
    var tr, r, l;
     r <- None;
     if (a \in senv) {
       l <@ ISem.step();
       tr <@ APIsec.sim_out(oget (senv.[a]), oget (oget l).`leakage);
       r <- Some tr;
     }
    return r;
  }

  proc sop(sop: sop_t, pargs: value_t list, sargs: svar_t list, a : svar_t) : sideInfo_t option = {
    var y, tr, l, r;
     r <- None;
     if (forall x, x \in sargs /\ x \in senv) {
       l <@ ISem.step();
       (y, tr) <@ APIsec.sim_sop(sop, pargs, map (fun a => oget senv.[a]) sargs, (oget l).`leakage);
       senv <- senv.[ a <- y ];
       r <- Some tr;
     }
    return r;
  }
}.*)

section Security.

local module IdealSem = IdealFunctionality(API_Ideal).
local module RealSem = ProgSem(API_Real).

(*local module SimSem = SimulatorSemantics.ProgSem(Simulator(H,IdealSem)).*)

local module Simulator (ISem : IdealInterface): MultiPartySemantics.AdvSemInterface = {
 (* Simulator runs a local copy of all parties... *)
 (*module RSem = RealSem
 module ISem = IdealSem*)

 (* secret state from corrupted parties *)
 var senv : (svar_t, sharedValue_t) fmap

  proc init(P1:L1.L, P2:L2.L, P3:L3.L): unit = {
    IdealSem.init(P1);
    senv <- empty;
  }
  (* [stepP] rely on the local [RealSem] module to .
     It also keeps the ISem synchronized with party 1 *)
  proc stepP(id: partyId_t): bool = {
    var r, x;
    r <- RealSem.stepP(id);
    if (id = P1 /\ r) { x <@ IdealSem.step(); }
    return r;
  }
 (* Step Secret *)
  proc stepS(): sideInfo_t option = {
    var v, tr, l, yy, y;
    var r <- None;
    var ecall <- syncPoint (allECalls RealSem.st);
    if (ecall <> None) { (* call to the API *)
      (* call the Ideal world [step] method *)
 (*      r <@ ISem.step();
      (* now, call the atomic simulators and keep the emulated parties' state synchronized *)
      if (r <> None) {*)
        match (oget ecall) with
        | Call_declass a =>
          { 
            if (a \in senv) {
              l <@ ISem.step();
              (v,tr) <@ APIsec.sim_declass(oget (senv.[a]), oget (oget l).`leakage);
              (* updates API result *)
              RealSem.st <- upd_SigmaAPI (Some v) RealSem.st;
              r <- Some tr;
            } }
        | Call_in a =>
          { if (ib RealSem.st <> None) {
              r <- None;
              l <@ ISem.step();
              tr <@ APIsec.sim_in(oget (oget l).`leakage);
              senv <- senv.[ a <- take t (oget (ib RealSem.st)) ];
              r <- Some tr;
              RealSem.st <- upd_ib None RealSem.st;
              RealSem.st <- upd_SigmaAPI None RealSem.st; (* resets call *)
            } } 
        | Call_out a =>
          { if (ob RealSem.st = None) {
              if (a \in senv) {
                l <@ ISem.step();
                yy <- oget (ob IdealFunctionality.st);
                (*tr <@ APIsec.sim_out(oget (senv.[a]), oget (oget l).`leakage);*)
                (*yy <$ nshr SecretSharingScheme.n (oget (API_Ideal.senv.[a]));*)
                tr <@ APIsec.sim_out(oget (senv.[a]), oget (oget l).`leakage);
                r <- Some tr;
                RealSem.st <- upd_ob (Some yy) RealSem.st;
                RealSem.st <- upd_SigmaAPI None RealSem.st; (* resets call *)
              } } }
        | Call_sop sop a pargs sargs =>
          { if (forall x, x \in sargs /\ x \in senv) {
              l <@ ISem.step();
              (y, tr) <@ APIsec.sim_sop(sop, pargs, map (fun a => oget senv.[a]) sargs, (oget l).`leakage);
              senv <- senv.[ a <- y ];
              r <- Some tr;
              RealSem.st <- upd_SigmaAPI None RealSem.st;
            } }
        end;
      }
    return r;
  }
}.

import MultiPartySemantics.

local module RealGame (Z: MultiPartySemantics.Environment) (A: MultiPartySemantics.Adversary) = MultiPartySemantics.Eval(RealSem,Z,A).

local module EnvironmentSemanticsInterface1 (Sem : Semantics) (ISem : IdealInterface) (A : Adversary) = {
 include Sem [-init, setInput, getOutput]
 proc init(P1 : L1.L, P2 : L2.L, P3 : L3.L) : unit = {
   Sem.init(P1,P2,P3);
   Simulator(ISem).init(P1,P2,P3);
 }
  proc setInput (x: L3.secret_t): bool = {
    var r;
    r <@ Sem.setInput(x);
    if (r) IdealSem.setInput(x);
    return r;
 }
 proc getOutput(): L3.secret_t option = {
   var r;
   r <@ Sem.getOutput();
    if (r <> None) IdealSem.getOutput();
   return r;
 }
 proc activate(): sideInfo_t option = {
   var r;
   r <@ A(Simulator(ISem)).step();
   return r;
 }
}.

local module IEval(Sem : Semantics, ISem : IdealInterface, Z : Environment, A : Adversary) = {
 proc eval(P1 : L1.L, P2 : L2.L, P3 : L3.L) = {
   var b;
   EnvironmentSemanticsInterface1(Sem,ISem,A).init(P1,P2,P3);
   b <@ Z(EnvironmentSemanticsInterface1(Sem,ISem,A)).animate();
   return (b);
 }
}.


local module IdealGame (Z: MultiPartySemantics.Environment) (A: MultiPartySemantics.Adversary) = IEval(RealSem,IdealFunctionality(API_Ideal),Z,A).

declare module Z : Environment {ProgSem,API_Ideal,Simulator,API_Real,Simulator}.
declare module A : Adversary {ProgSem,Z,Simulator,API_Real}.

local equiv Security:
RealGame(Z, A).eval ~ IdealGame(Z, A).eval : ={P1, P2, P3, glob Z, glob A} ==> ={res}.
proof.
proc.
inline*.
sp.
(** mexer na configuração da funcionalidade ideal diretamente com o simulador em vez de parametro *)
call (_ : ={glob A, glob ProgSem} /\ 
 (forall v, v \in API_Real.senv{1} <=> v \in API_Ideal.senv{2}) /\
 (forall v, v \in API_Real.senv{1} <=> v \in Simulator.senv{2}) /\
 (forall v, v \in API_Real.senv{1} => API_Ideal.senv{2}.[v] = Some (unshr (oget API_Real.senv{1}.[v]))) /\
 (forall v, v \in API_Real.senv{1} => oget Simulator.senv{2}.[v] = take t (oget API_Real.senv{1}.[v])) /\
 ProgSem.st{1}.`StP1 = IdealFunctionality.st{2}.`sigma /\
 ProgSem.st{1}.`ib = IdealFunctionality.st{2}.`ib /\
 ProgSem.st{1}.`ob = IdealFunctionality.st{2}.`ob
 ).

proc; inline*.
sp 2 2.
if => //=.
rcondt{2} 4.
move => &m.
by wp; skip.
rcondt{2} 6.
move => &m.
by wp; skip => /#.
by wp; skip.
rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

proc; inline*.
sp 1 1.
if => //=.
rcondt{2} 3.
move => &m.
by wp; skip.
rcondt{2} 4.
move => &m.
by wp; skip => /#.
by wp; skip.
rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

proc; inline*.
call (_ : ={glob ProgSem} /\ 
 (forall v, v \in API_Real.senv{1} <=> v \in API_Ideal.senv{2}) /\
 (forall v, v \in API_Real.senv{1} <=> v \in Simulator.senv{2}) /\
 (forall v, v \in API_Real.senv{1} => API_Ideal.senv{2}.[v] = Some (unshr (oget API_Real.senv{1}.[v]))) /\
 (forall v, v \in API_Real.senv{1} => oget Simulator.senv{2}.[v] = take t (oget API_Real.senv{1}.[v])) /\
 ProgSem.st{1}.`StP1 = IdealFunctionality.st{2}.`sigma /\
 ProgSem.st{1}.`ib = IdealFunctionality.st{2}.`ib /\
 ProgSem.st{1}.`ob = IdealFunctionality.st{2}.`ob
 ).

proc; inline*.
sp.
match => //=.
if => //=. 
sp 1 1.
if => //=. 
rcondt{2} 4.
move => &m.
by wp; skip.
rcondt{2} 7.
move => &m.
by wp; skip => /#.
rcondt{2} 8.
move => &m.
by wp; skip => /#.
wp; skip; progress.
rewrite /progSt /envSt /resSt => //=.
by rewrite !H3 => /#.
by rewrite !H3 => /#.
by rewrite !H3 => /#.
by rewrite !H3 => /#.
by rewrite !H3 => /#.

rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

if => //=.
rcondf{2} 4.
move => &m.
by wp; skip.
by wp; skip.
rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

if => //=.
rcondf{2} 4.
move => &m.
by wp; skip.
by wp; skip.
rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

proc.
sp 2 2.
if => //=.
match => //=.
move => *.
inline API_Real.declass IdealFunctionality(API_Ideal).step.
sp 2 0.
if => //=.
smt().
rcondf{2} 4.
move => &m.
by wp; skip => /#.
sp 0 3.
match{2} => //=.
move => *.
inline API_Ideal.declass.
rcondt{2} 3.
move => &m.
by wp; skip => /#.
rcondt{2} 6.
move => &m.
by wp; skip.
rcondt{1} 4.
move => &m.
by auto.
wp; sp.
symmetry.
exists* (oget API_Real.senv{2}.[a]).
elim*.
progress.
exists* (oget (oget (Some (snd (oget (Some (v0{1}, Leak (oget API_Ideal.senv{1}.[a1]))))))).`leakage).
elim* => *.
call (assumption_declass f f0).
skip; progress.
smt(). 
smt().
smt().
smt().
smt().
smt().

move => *.
exfalso => /#.
move => *.
exfalso => /#.
move => *.
exfalso => /#.

sp 1 1.
if{1} => //=.
by wp; skip.


move => *.
inline API_Real.input IdealFunctionality(API_Ideal).step.
if => //=.
rcondf{2} 5.
move => &m.
by wp; skip => /#.
sp 0 4.
match{2} => //=.
move => *.
exfalso => /#.
move => *.
inline API_Ideal.input.
rcondt{2} 1.
move => &m.
by skip => /#.
rcondt{2} 5.
move => &m.
by wp; skip.
rcondt{1} 6.
move => &m.
by auto.
wp; sp.
symmetry.
elim* => *.
exists* (oget (oget (Some (oget (Some (CorruptedShares (take t (oget st_R.`ib))))))).`leakage).
elim* => *.
call (assumption_in f).
skip; progress.
smt().
smt(mem_set).
smt(mem_set).
smt(mem_set).
smt(mem_set).
smt(mem_set get_setE).
smt(mem_set get_setE).
smt().
smt().

move => *.
exfalso => /#.
move => *.
exfalso => /#.


move => *.
if => //=.
inline API_Real.output IdealFunctionality(API_Ideal).step.
sp 2 0.
if => //=.
smt().
rcondf{2} 4. 
move => &m.
by wp; skip => /#.
sp 0 3.
match{2}.
move => *.
exfalso => /#.
move => *.
exfalso => /#.
move => *.
rcondt{2} 1.
move => &m.
by skip => /#.
inline API_Ideal.output.
rcondt{2} 3.
move => &m.
by wp; skip => /#.
rcondt{2} 6.
move => &m.
by auto.
rcondt{1} 4.
move => &m.
by auto.
wp.
sp.
seq 0 1 : (#pre /\ yy0{2} \in nshr SecretSharingScheme.n (oget API_Ideal.senv{2}.[a])).
rnd{2}; skip; progress.
apply nshr_ll.
smt().
sp.
elim* => *.
exists* (yy0{2}).
elim* => *.
(*exists* (oget (oget (Some (snd (oget (Some (yy0_R, CorruptedShares (take t yy0_R))))))).`leakage).
elim* => *.*)
exists* (oget (API_Real.senv{1}.[a])).
elim* => *.
symmetry.
call (assumption_out yy0_R).
skip; progress.
smt().
smt().
smt().
smt().

move => *.
exfalso => /#.

rcondf{1} 2.
move => &m.
by wp; skip.
by wp; skip.



move => *.
inline API_Real.sop IdealFunctionality(API_Ideal).step.
sp 5 0.
if => //=.
smt().
rcondf{2} 4.
move => &m.
by wp; skip => /#.
sp.
match{2}.
move => *.
exfalso => /#.
move => *.
exfalso => /#.
move => *.
exfalso => /#.
move => *.
inline API_Ideal.sop.
rcondt{2} 6.
move => &m.
by wp; skip => /#.
rcondt{2} 10.
move => &m.
by wp; skip => /#.
rcondt{1} 5.
move => &m.
by auto.
wp.
sp.
elim* => *.
exists* (map (fun x => oget API_Real.senv{1}.[x]) sargs).
elim* => ?.
exists* ((oget (Some (oget (Some {| leakage = snd (MPCProtocolLibrary.sop_spec sop pargs (map (fun (x0 : svar_t) => oget senv_R.[x0]) sargs)); trace = []; |})))).`leakage).
elim* => ?.
symmetry.
call (assumption_sop o pargs f f0).
symmetry.
skip; progress.
smt().
smt().
smt().
rewrite -map_comp /(\o) => //=.
cut ->: (fun (x : svar_t) =>
          (SecretSharingScheme.unshr (oget API_Real.senv{1}.[x]))) = 
        (fun (x : svar_t) => oget senv_R.[x]).
rewrite fun_ext /(==) => *.
smt().
smt().
rewrite -map_comp /(\o) => //=.
smt().
smt(mem_set).
smt(mem_set).
smt(mem_set).
smt(mem_set).
move : H16.
rewrite -map_comp /(\o) => //=.
cut ->: (fun (x : svar_t) =>
          (SecretSharingScheme.unshr (oget API_Real.senv{1}.[x]))) = 
        (fun (x : svar_t) => oget senv_R.[x]).
rewrite fun_ext /(==) => *.
smt().
smt(mem_set get_setE).
move : H16.
rewrite -map_comp /(\o) => //=.
cut ->: (fun (x : svar_t) =>
          (SecretSharingScheme.unshr (oget API_Real.senv{1}.[x]))) = 
        (fun (x : svar_t) => oget senv_R.[x]).
rewrite fun_ext /(==) => *.
smt().
smt(mem_set get_setE).
smt(mem_set get_setE).
smt().
smt().
smt().

rcondf{1} 2.
move => &m.
by wp; skip.
by wp; skip.

by wp; skip.

skip; progress.
smt(mem_empty).
smt(mem_empty).
smt(mem_empty).
smt(mem_empty).
qed.

end section Security.

end Security.

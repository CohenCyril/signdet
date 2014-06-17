Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice path fintype finset finfun.
Require Import div bigop ssralg poly polydiv ssrnum perm zmodp ssrint tuple.
Require Import interval matrix mxtens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def Pdiv.Ring Pdiv.ComRing.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Section SignDet.

(* Set Printing All. *)

(* Fixpoint signdet (n : nat) (taq : ('I_n -> 'I_3) -> int) {struct n} : *)
(*   {m : nat & (m.-tuple 'I_3 * m.-tuple 'I_3 * 'M[int]_m)%type} := *)
(*   match n with *)
(*     | 0     => (existT _ 0 ([tuple], [tuple], 0%R)) *)
(*     | n'.+1 =>  *)
(*       let taq' (f : 'I_n' -> 'I_3) :=  *)
(*             taq (fun (i : 'I_n) =>  *)
(*                    if (i < n') =P true is ReflectT P *)
(*                    then f (Ordinal P) else ord0) in *)
(*       let: existT m (sc, ada, M) := signdet taq' in *)
               
(*                (existT _ 0 ([tuple], [tuple], 0%R)) *)
(*   end. *)

Definition extend n (X : finType) (x : X) (S : {set {ffun 'I_n -> X}}) :
   {set {ffun 'I_n.+1 -> X}} :=
   [set s : {ffun 'I_n.+1 -> X} | (s ord_max == x)
   && ([ffun x : 'I_n => s (lift ord_max x)] \in S)].

Definition tvec (n : nat) (taq : ('I_n -> 'I_3) -> int) (a : {set {ffun 'I_n -> 'I_3}}) :
   'rV[int]_(#|a|).
Admitted.

Definition cnonnull (n m : nat) (s : {set {ffun 'I_n -> 'I_3}}) (c : 'rV[int]_(3 * m)) :
   {set {ffun 'I_n.+1 -> 'I_3}}. (* morally m = #|s| *)
Admitted.

Definition ctmat1 := \matrix_(i < 3, j < 3)
  (nth [::] [:: [:: 1%:Z ; 1 ; 1 ]
              ; [:: -1   ; 1 ; 1 ]
              ; [::  0   ; 0 ; 1 ] ] i)`_j.


Lemma mul2n n : (2 * n = n + n)%N. Proof. by rewrite mulSn mul1n. Qed.
Lemma mul3n n : (3 * n = n + (n + n))%N. Proof. by rewrite !mulSn addn0. Qed.

Definition lexi n (s : {set {ffun 'I_n -> 'I_3}}) : 'I_(#|s|) -> {ffun 'I_n -> 'I_3}.
Admitted.

Definition sign (i : 'I_3) : int :=
  if i == ord0 then -1 else if i == ord_max then 1 else 0.
Definition expo (i : 'I_3) : nat :=
  if i == ord0 then 0%N else if i == ord_max then 2%N else 1%N.

Definition mat n (s : {set {ffun 'I_n -> 'I_3}}) (a : {set {ffun 'I_n -> 'I_3}}) :
  'M[int]_(#|s|, #|a|) := \matrix_(i,j) \prod_k (sign (@lexi _ s i k)) ^+ (expo (@lexi _ a j k)).

Definition adapted n (s : {set {ffun 'I_n -> 'I_3}}) (a : {set {ffun 'I_n -> 'I_3}}) :=
  (#|s| == #|a|) && (conform_mx (0 :'M[int]_(#|s|)) (mat s a) \in unitmx).

Definition adapt n (s : {set {ffun 'I_n -> 'I_3}}) : {set {ffun 'I_n -> 'I_3}}.
Admitted.

Definition nonEmptySigns n (taq : ('I_n -> 'I_3) -> int) : {set {ffun 'I_n -> 'I_3}}.
Admitted.

Definition signdet (n : nat) (taq : ('I_n -> 'I_3) -> int)  :
  {sa : {set {ffun 'I_n -> 'I_3}} * {set {ffun 'I_n -> 'I_3}}
        & 'M[int]_(#|sa.1|, #|sa.2|)}.
Proof.
elim: n taq.
  move=> taq; exists (set0, set0); exact 0.
move=> n' IHn taq.
set taq' := fun f => taq (fun (i : 'I_n'.+1) => 
                 if (i < n')%N =P true is ReflectT P
                   then f (Ordinal P) else ord0).
have [[s a] /= M] := IHn taq'.
set s' := cnonnull s (row_mx (tvec taq (extend ord0 a))
                 (row_mx (tvec taq (extend (1%R : 'F_3) a)) (tvec taq (extend (2%:R : 'F_3) a))) *m 
               castmx (mul3n _, erefl) (invmx (M *t ctmat1))).

 :=
  match n with
    | 0     => (existT (fun sa : {set {ffun 'I_n -> 'I_3}} * {set {ffun 'I_n -> 'I_3}}
                         => 'M[int]_(#|sa.1|, #|sa.2|)) (set0, set0) 0%R)
    | n'.+1 => 
      let taq' (f : 'I_n' -> 'I_3) := 
          taq (fun (i : 'I_n) => 
                 if (i < n')%N =P true is ReflectT P
                   then f (Ordinal P) else ord0) in
      let: existT (s, a) M := signdet taq' in
      let c := cnonnull s (row_mx (tvec taq (extend ord0 a))
                 (row_mx (tvec taq (extend 1%R a)) (tvec taq (extend 2%R a))) *m 
               castmx (mul3n _, erefl) (invmx (M *t ctmat1))) in



      (* let s' :=  (extend 0%R s) :|: (extend 1%R s) :|: (extend 2%R s) in *)
      (* let a' :=  (extend 0%R a) :|: (extend 1%R a) :|: (extend 2%R a) in *)


 (existT (fun sa : {set {ffun 'I_n -> 'I_3}} * {set {ffun 'I_n -> 'I_3}}
                         => 'M[int]_(#|sa.1|, #|sa.2|)) (set0, set0) 0%R)
  end.

Definition signdetS (n : nat) (taq : ('I_n -> 'I_3) -> int) :=
  let: existT sa _ := signdet taq in sa.1.

Definition signdetAda (n : nat) (taq : ('I_n -> 'I_3) -> int) :=
  let: existT sa _ := signdet taq in sa.2.

Definition signdetM_subdef (n : nat) (taq : ('I_n -> 'I_3) -> int) :
  'M[int]_(#|signdetS taq|,#|signdetAda taq|).
Admitted.

Lemma signdet_sizeP (n : nat) (taq : ('I_n -> 'I_3) -> int) :
  #|signdetS taq| = #|signdetAda taq|.
Proof.
Admitted.

Definition signdetM  (n : nat) (taq : ('I_n -> 'I_3) -> int) :
  'M[int]_(#|signdetS taq|,#|signdetS taq|) :=
  castmx (erefl, esym (signdet_sizeP taq)) (signdetM_subdef taq).

Lemma unit_signdet  (n : nat) (taq : ('I_n -> 'I_3) -> int) : 
  signdetM taq \in unitmx.
Proof.
Admitted.


  (* {m : nat & m.-tuple 'I_3 * m.-tuple 'I_3 * 'M[int]_m)%type} := *)
  (* match n with *)
  (*   | 0     => (existT _ 0 ([tuple], [tuple], 0%R)) *)
  (*   | n'.+1 =>  *)
  (*     let taq' (f : 'I_n' -> 'I_3) :=  *)
  (*           taq (fun (i : 'I_n) =>  *)
  (*                  if (i < n') =P true is ReflectT P *)
  (*                  then f (Ordinal P) else ord0) in *)
  (*     let: existT m (sc, ada, M) := signdet taq' in *)
               
  (*              (existT _ 0 ([tuple], [tuple], 0%R)) *)
  (* end. *)


End SignDet.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice path fintype finset finfun.
From mathcomp Require Import div bigop ssralg poly polydiv ssrnum perm.
From mathcomp Require Import zmodp ssrint rat tuple prime.
From mathcomp Require Import interval matrix mxalgebra binomial.
From mathcomp Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def Pdiv.Ring Pdiv.ComRing.

Local Open Scope ring_scope.
Local Open Scope nat_scope.

Section extrassr.

Lemma fintype1 (T : finType) (x : T) : #|T| = 1 -> all_equal_to x.
Proof.
move=> /eqP T1 y /=; apply: contraTeq T1 => neq_yx.
suff: #|T| >= #|[set y; x]| by rewrite cards2 neq_yx => /gtn_eqF ->.
by apply/subset_leqif_card/subsetP=> z /set2P [] ->; rewrite inE.
Qed.

Lemma reindex_enum_cond (R : Type) (idx : R) (op : Monoid.com_law idx)
  (X : finType) (S : {set X}) s0 (s0S : s0 \in S)
  (P : pred 'I_#|S|) (F : 'I_#|S| -> R) (h := enum_rank_in s0S) :
  \big[op/idx]_(i < #|S| | P i) F i = \big[op/idx]_(s in S | P (h s)) F (h s).
Proof.
rewrite /h {h} (reindex (enum_val : 'I_#|S| -> _)).
apply: eq_big => [i|i Pi]; rewrite enum_valK_in ?enum_valP //.
exists (enum_rank_in s0S) => [i|s]; rewrite -topredE /=.
  by rewrite enum_valK_in.
by move=> /andP [sS _]; rewrite enum_rankK_in.
Qed.

Lemma reindex_enum (R : Type) (idx : R) (op : Monoid.com_law idx)
  (X : finType) (S : {set X}) s0 (s0S : s0 \in S)
  (F : 'I_#|S| -> R) (h := enum_rank_in s0S) :
  \big[op/idx]_(i < #|S|) F i = \big[op/idx]_(s in S) F (h s).
Proof.
rewrite (reindex_enum_cond _ s0S).
by apply: eq_big=> //= s; rewrite andbT.
Qed.

Lemma row_free_inj (F : fieldType) (m n p : nat) (A : 'M[F]_(n, p)) :
  row_free A -> injective (mulmxr A : 'M_(m, n) -> _).
Proof. exact: row_free_inj. Qed.

Lemma inj_row_free (F : fieldType) (n p : nat) (A : 'M[F]_(n, p)) :
  (forall v : 'rV_n, v *m A = 0%R -> v = 0%R) -> row_free A.
Proof.
move=> Ainj; rewrite -kermx_eq0; apply/eqP.
apply/row_matrixP => i; rewrite row0; apply/Ainj.
by rewrite -row_mul mulmx_ker row0.
Qed.

Lemma det_mx11 (R : comRingType) (M : 'M[R]_1) : \det M = M 0%R 0%R.
Proof. by rewrite {1}[M]mx11_scalar det_scalar. Qed.

End extrassr.

Section ExtX.

Variables (n : nat) (X : finType).
Implicit Types (S : {set X ^ n.+1}) (R : {set X ^ n}).
Implicit Types (s : X ^ n.+1) (r : X ^ n) (x y : X) (m : nat).

(* Extension of s with one element x at the end *)
Definition extelt x r : X ^ n.+1 := [ffun i => oapp r x (unlift 0%R i)].

(* Restriction of b, without the last element, the inverse of extelt *)
Definition restrict s : X ^ n := [ffun i => s (lift 0%R i)].

(* extension of a set with one element x at the end. *)
Definition extset x R : {set X ^ n.+1} := [set extelt x s | s in R].

(* the set of possible extensions of s in S *)
Definition exts S (s : X ^ n) : {set X} := [set x | extelt x s \in S].

(* the set of elements with at least m extensions in S,
  Xi 1 is the inverse of restrict *)
Definition Xi m S : {set X ^ n} := [set s | m <= #|exts S s|].

Lemma restrictK s : extelt (s 0%R) (restrict s) = s.
Proof.
by apply/ffunP=> i; rewrite ffunE; case: unliftP => [j|] ->; rewrite //= ffunE.
Qed.

Lemma exteltK x : cancel (extelt x) restrict.
Proof. by move=> b; apply/ffunP=> i; rewrite !ffunE liftK. Qed.

Lemma restrictP S s r : reflect (exists i, s = extelt i r) (restrict s == r).
Proof.
apply: (iffP eqP) => [<-|[i ->]]; last by rewrite exteltK.
by exists (s 0%R); rewrite restrictK.
Qed.

Lemma extelt0 x r : extelt x r 0%R = x.
Proof. by rewrite /extelt ffunE unlift_none. Qed.

Let extE := (inE, extelt0, exteltK, restrictK, eqxx).

Lemma eq_extelt x x' (r r' : X ^ n) :
  (extelt x r == extelt x' r') = (x == x') && (r == r').
Proof.
have [->|] /= := altP (x =P x'); first by rewrite (can_eq (@exteltK _)).
apply: contraNF => /eqP /(congr1 (fun u : _ ^ _ => u 0%R)).
by rewrite !extelt0 => ->.
Qed.

Lemma exts0 r : exts set0 r = set0.
Proof. by apply/setP=> i; rewrite !inE. Qed.

Lemma card_exts S r : #|exts S r| <= #|X|.
Proof. by rewrite subset_leq_card //; apply/subsetP. Qed.

Lemma extelt_in S r x : (extelt x r \in S) = (x \in exts S r).
Proof. by rewrite inE. Qed.

Lemma card_extset R x : #|extset x R| = #|R|.
Proof.
by rewrite card_imset // => u v /eqP; rewrite eq_extelt => /andP [_ /eqP].
Qed.

Lemma mem_extset x s R : s \in extset x R = (s 0%R == x) && (restrict s \in R).
Proof.
apply/imsetP/idP => [[r rS ->]|/andP [/eqP<-] rsS]; first by rewrite !extE.
by exists (restrict s) => //; rewrite !extE.
Qed.

Lemma mem_extset_r x r R : extelt x r \in extset x R = (r \in R).
Proof. by rewrite mem_extset ?extE. Qed.

Lemma restrict_inW S s : s \in S -> restrict s \in Xi 1 S.
Proof.
by move=> sS; rewrite inE; apply/card_gt0P; exists (s 0%R); rewrite !extE.
Qed.

Lemma extset0 x : extset x set0 = set0 :> {set X ^ n.+1}.
Proof. by rewrite /extset imset0. Qed.

Lemma extsetK x : cancel (extset x) (Xi 1).
Proof.
move=> S; apply/setP => /= s; apply/idP/idP => [|sS]; last first.
  by rewrite -[s](exteltK x) restrict_inW // mem_extset_r.
by rewrite inE => /card_gt0P [y]; rewrite inE mem_extset ?extE => /andP [].
Qed.

Fact ord0_in_exts (S : {set X ^ n.+1})
  (s : X ^ n.+1) : s \in S -> s 0%R \in exts S (restrict s).
Proof. by rewrite !extE. Qed.

Lemma extset_eq0 x (S : {set X ^ n}) : (extset x S == set0) = (S == set0).
Proof. by rewrite -(extset0 x) (can_eq (extsetK _)). Qed.

Lemma eq_extset x y R R' :
  (extset x R == extset y R') = ((R' != set0) ==> (x == y)) && (R == R').
Proof.
have [->|[r rR]] /= := set_0Vmem R'; [by rewrite extset0 eqxx /= extset_eq0|].
have /set0Pn -> /= : exists r, r \in R' by exists r.
have [<-|/=] := altP (x =P y); first by rewrite (can_eq (extsetK _)).
apply: contraNF => /eqP eq_xS_yR; have := mem_extset_r y r R'.
by rewrite -eq_xS_yR rR eq_sym mem_extset ?extE => /andP [].
Qed.

Lemma subset_extset x R R' : (extset x R \subset extset x R') = (R \subset R').
Proof.
apply/subsetP/subsetP => RR' /= r.
  by move/(mem_imset (extelt x))/RR'; rewrite mem_extset_r.
by case/imsetP=> r' rR ->; rewrite mem_extset_r RR'.
Qed.

Lemma subset_exts r : {homo exts^~ r : S S' / S \subset S'}.
Proof. by move=> ???; apply/subsetP=> x; rewrite !inE; apply/subsetP. Qed.

Lemma subset_Xi m : {homo @Xi m : S S' / S \subset S'}.
Proof.
move=> S S' subSS'; apply/subsetP=> s; rewrite !in_set => /leq_trans-> //.
exact/subset_leq_card/subset_exts.
Qed.

Lemma leq_Xi S : {homo Xi^~ S : m p / p <= m >-> m \subset p}.
Proof. by move=> m p ?; apply/subsetP => s; rewrite !inE; apply/leq_trans. Qed.

Lemma leq_exts S r m : (m <= #|exts S r|) = (r \in Xi m S).
Proof. by rewrite inE. Qed.

Lemma Xi0s S : Xi 0 S = [set: X ^ n].
Proof. by apply/setP => i; rewrite inE. Qed.

Lemma Xi0 i : i > 0 -> Xi i set0 = set0.
Proof. by case: i => // i _; apply/setP => e; rewrite !inE exts0 cards0. Qed.

Lemma Xi1_eq0  S : (Xi 1 S == set0) = (S == set0).
Proof.
apply/idP/idP=> [|/eqP->]; last by rewrite Xi0.
apply: contraTT => /set0Pn [x xS].
by apply/set0Pn; exists (restrict x); apply: restrict_inW.
Qed.

Lemma Xi_eq0 S i : (Xi i.+1 S == set0) = [forall s, #|exts S s| <= i].
Proof.
apply/eqP/forallP => [XiiS_eq0 s|].
  apply: contra_eqT XiiS_eq0; rewrite -ltnNge => i_small.
  by apply/set0Pn; exists s; rewrite inE.
move=> few_s; apply: contraTeq isT => /set0Pn /= [s].
by rewrite inE ltnNge few_s.
Qed.

End ExtX.

Section ExtIk.

Variable (k n : nat).
Let X := 'I_k.
Implicit Types (S : {set X ^ n.+1}) (R : {set X ^ n}).
Implicit Types (s : X ^ n.+1) (r : X ^ n) (x y : X) (m : nat) (i j : 'I_k).

Definition extXE := (inE, extelt0, exteltK, restrictK, eqxx,
             mem_extset, extsetK, extset0).

Program Definition tupleext S r :=
  @Tuple k _ (sort (fun i j => val i <= val j) (enum (exts S r))
                   ++ enum (~: exts S r)) _.
Next Obligation.
rewrite size_cat ?size_sort -!cardE -cardsUI addnC.
set A := _ :|: _; set B := _ :&: _.
suff [-> ->] : (A = setT) /\ (B = set0) by rewrite cardsT card_ord cards0.
by split; apply/setP => i; rewrite !inE ?andbN ?orbN.
Qed.

Lemma tupleext_uniq S r : uniq (tupleext S r).
Proof.
rewrite cat_uniq ?sort_uniq ?enum_uniq andbT; apply/hasPn=> x.
by rewrite /= mem_sort !mem_enum !inE.
Qed.

Lemma mem_tupleext S r x : x \in tupleext S r.
Proof. by rewrite mem_cat mem_sort !mem_enum !inE orbN. Qed.

(* The nth, last element of the extension of s in S *)
Definition nthext S r i : X := tnth (tupleext S r) i.

(* the inverse of nthext *)
Program Definition indexext S r x := @Ordinal k (index x (tupleext S r)) _.
Next Obligation.
by have := index_mem x (tupleext S r); rewrite mem_tupleext size_tuple.
Qed.

(* The nth extension in S *)
Definition reext S i : {set X ^ n.+1} :=
  [set extelt (nthext S r i) r | r in Xi i.+1 S].

Lemma nthextK S r : cancel (nthext S r) (indexext S r).
Proof.
move=> i; apply/val_inj; rewrite /= /indexext index_uniq ?tupleext_uniq //.
by rewrite size_tuple ltn_ord.
Qed.

Lemma indexextK S r : cancel (indexext S r) (nthext S r).
Proof. by move=> x; rewrite /nthext /tnth nth_index // mem_tupleext. Qed.

Definition extE := (extXE, indexextK, nthextK).

Lemma nthext_in S r i : (nthext S r i \in exts S r) = (i < #|exts S r|).
Proof.
rewrite /nthext /tnth nth_cat size_sort -!cardE.
have [i_small|i_big] //= := ltnP i _.
  rewrite -mem_enum -(mem_sort (fun i j => val i <= val j)).
  by rewrite mem_nth ?size_sort -?cardE.
apply: negbTE; rewrite -in_setC -mem_enum mem_nth // -?cardE.
by rewrite -subSn // leq_subLR cardsC card_ord.
Qed.

Lemma in_exts S r x : (x \in exts S r) = (indexext S r x < #|exts S r|).
Proof. by rewrite -nthext_in indexextK. Qed.

Lemma nthext_inj S r : injective (nthext S r).
Proof. exact: can_inj (@nthextK _ _). Qed.

Lemma exts_leq S r : #|exts S r| <= k.
Proof. by rewrite (leq_trans (card_exts _ _)) ?card_ord. Qed.
Hint Resolve exts_leq.

Lemma exts_restrict_neq0 S s : s \in S -> exts S (restrict s) != set0.
Proof.
move=> sS; have : s 0%R \in exts S (restrict s) by rewrite inE ?restrictK.
by apply: contraTneq => ->; rewrite inE.
Qed.

Lemma in_Xi_small S r i : (r \in Xi i.+1 S) = (nthext S r i \in exts S r).
Proof. by rewrite in_exts nthextK leq_exts. Qed.

Lemma in_Xi_big S r m : m > k -> (r \in Xi m S) = false.
Proof. by rewrite ltnNge -leq_exts; apply/contraNF => /leq_trans ->. Qed.

Lemma card_reext S i : #|reext S i| = #|Xi i.+1 S|.
Proof.
rewrite card_in_imset //= => x y xXi yXi /eqP.
by rewrite eq_extelt => /andP [_ /eqP].
Qed.

Lemma reext_inj S :
  {in [pred m : 'I_k | Xi m.+1 S != set0] &, injective (reext S)}.
Proof.
move=> i j /= _ Xij_neq0; have /set0Pn [/= s'1 s'1Xi]:= Xij_neq0.
pose f i r := (extelt (nthext S r i) r) => /setP /(_ (f j s'1)).
rewrite (mem_imset (f j) s'1Xi) /f => /imsetP [/= s'2 s'2Xi] /eqP.
by rewrite eq_extelt andbC => /andP [/eqP -> /eqP /nthext_inj].
Qed.

Lemma subset_reext S i : reext S i \subset S.
Proof.
by apply/subsetP=> j /imsetP [/= ??->]; rewrite extelt_in nthext_in leq_exts.
Qed.

Lemma reext_eq0 S i : (reext S i == set0) = (Xi i.+1 S == set0).
Proof. by rewrite -!cards_eq0 card_reext. Qed.

Lemma reext0 i : @reext set0 i = set0.
Proof.
apply/setP=> j; rewrite !inE; apply/negP => /imsetP /= [x].
by rewrite Xi0 ?inE.
Qed.

Lemma reextE S i :
  reext S i = [set s in S | indexext S (restrict s) (s 0%R) == i].
Proof.
apply/setP => s; rewrite !inE; have [sS|sNS] /= := boolP (s \in S); last first.
  by apply:contraNF sNS; apply/subsetP/subset_reext.
apply/imsetP/eqP => /= [[s' s'Xi ->]|<-].
  by rewrite extelt0 exteltK nthextK.
by exists (restrict s); rewrite ?in_Xi_small ?indexextK ?extXE.
Qed.

Lemma reextT S : S = \bigcup_i reext S i.
Proof.
apply/setP => s; apply/idP/bigcupP => [sS|]; last first.
  move=> [i _ /imsetP [x]]; rewrite inE => i_small ->.
  by rewrite extelt_in nthext_in.
exists (indexext S (restrict s) (s 0%R)) => //.
by apply/imsetP; exists (restrict s); rewrite ?extE // -in_exts ?extE.
Qed.

Lemma reextTW S : S = \bigcup_(i < k | Xi i.+1 S != set0) reext S i.
Proof.
rewrite [LHS]reextT /= (bigID (fun i : 'I__ => Xi i.+1 S == set0)) /=.
by rewrite big1 ?set0U // => i; rewrite -reext_eq0 => /eqP.
Qed.

Lemma partition_reext S :
  partition [set reext S i | i in 'I_k & Xi i.+1 S != set0] S.
Proof.
apply/and3P; split; [apply/eqP| |apply/imsetP]; last 1 first.
- by move=> [/= i]; rewrite !inE /= -reext_eq0 eq_sym => /eqP.
- symmetry; rewrite cover_imset [LHS]reextTW.
  by apply: eq_bigl => /= i; rewrite inE.
apply/trivIsetP => /= _ _ /imsetP [i Xii_neq0 ->] /imsetP [j Xij_neq0 ->].
apply: contraNT; rewrite -setI_eq0 => /set0Pn [/= s]; rewrite !inE.
by rewrite !reextE !inE -!andbA => /and4P [_ /eqP -> _ /eqP ->].
Qed.

End ExtIk.

Section AbstractSigndet.

Variable k' : nat.
Let k := k'.+1.
Variable M : 'M[rat]_k.

Let Sgn n := ('I_k ^ n)%type.
Let Exp n := ('I_k ^ n)%type.
Let X := 'I_k.

Definition mat1 (S : {set X}) : 'M[rat]_#|S| :=
  \matrix_(i, j) M (enum_val i) (inord j).

Hypothesis row_free_mat1 : forall (S : {set X}), row_free (mat1 S).

Definition mat_coef n (i : Sgn n) (j : Exp n) := (\prod_k M (i k) (j k))%R.

Lemma mat_coefS n (s : Sgn n.+1) (a : Exp n.+1) :
  mat_coef s a = (M (s 0%R) (a 0%R) * mat_coef (restrict s) (restrict a))%R.
Proof.
rewrite /mat_coef /= big_ord_recl; congr (_ * _)%R.
by apply: eq_bigr => i _; rewrite !ffunE.
Qed.

Definition mat n (S : {set Sgn n}) (A : {set Exp n}) :=
  \matrix_(i < #|S|, j < #|A|) mat_coef (enum_val i) (enum_val j).

Definition adapted n (S : {set Sgn n}) (A : {set Exp n}) :=
  (#|A| == #|S|) && row_free (mat S A).

Fixpoint adapt n (S : {set Sgn n}) : {set Exp n} :=
  match n return {set Sgn n} -> {set Exp n} with
    | 0     => fun S => S
    | n'.+1 => fun S => \bigcup_(i < k) extset i (adapt (Xi i.+1 S))
  end S.
Arguments adapt n S : simpl never.

Lemma adapt0 (S : {set Sgn 0}) : adapt S = S.
Proof. by []. Qed.

Lemma adaptS n (S : {set Sgn n.+1}) :
  adapt S = \bigcup_(i < k) extset i (adapt (Xi i.+1 S)).
Proof. by []. Qed.

Definition adaptE := (adapt0, adaptS).

Lemma adaptn0 n : @adapt n set0 = set0.
Proof.
elim: n => [|n IHn] //=; rewrite (adapt0, adaptS) big1 // => i _.
by rewrite Xi0 // IHn extset0.
Qed.

Lemma adapt_eq0 n S : (@adapt n S == set0) = (S == set0).
Proof.
elim: n => [|n IHn] // in S *.
apply/idP/idP => [/=|/eqP ->]; last by rewrite adaptn0.
apply: contraTT; rewrite -Xi1_eq0 -IHn => /set0Pn [x x_adaX].
apply/set0Pn; exists (extelt ord0 x).
by apply/bigcupP; exists 0%R => //; rewrite !extE.
Qed.

Lemma subset_adapt n (S S' : {set Sgn n}) :
  S \subset S' -> adapt S \subset adapt S'.
Proof.
elim: n => [//|n IHn] in S S' * => subSS' /=; apply/bigcupsP => i _.
by rewrite (bigcup_max i) // subset_extset IHn // subset_Xi.
Qed.

Lemma in_adapt n (S : {set Sgn n.+1}) (a : Exp n.+1) :
  (a \in adapt S) = (restrict a \in adapt (Xi (a 0%R).+1 S)).
Proof.
move=> /=; apply/bigcupP/idP => [[i _ /imsetP [s sAXi ->]]|].
  by rewrite ?extE.
by move=> ra; exists (a 0%R); rewrite ?extE.
Qed.

Lemma adapt_down_closed  n (S : {set Sgn n}) (a b : Exp n) :
  (forall i, b i <= a i)%N -> a \in adapt S -> b \in adapt S.
Proof.
elim: n => [|/= n IHn] in S a b *.
  by move=> _; rewrite (fintype1 b) // card_ffun !card_ord.
move=> leq_ba; rewrite !in_adapt => raAXi.
have: restrict b \in adapt (Xi (a 0%R).+1 S).
  by apply: IHn raAXi => i; rewrite !ffunE leq_ba.
by apply: subsetP; rewrite subset_adapt ?leq_Xi ?ltnS ?leq_ba.
Qed.

Lemma partition_adapt n (S : {set Sgn n.+1}) :
  partition [set extset i (adapt (Xi (i : X).+1 S))
            | i in X & Xi i.+1 S != set0] (adapt S).
Proof.
apply/and3P; split; [apply/eqP|apply/trivIsetP|apply/imsetP]; last 1 first.
- by move=> [i]; rewrite inE -adapt_eq0 -(extset_eq0 i) eq_sym => /eqP.
- rewrite adaptE (bigID [pred i : 'I__ | Xi i.+1 S == set0]) /=.
  rewrite big1 ?set0U; last by move=> i /eqP ->; rewrite adaptn0 extset0.
  by rewrite cover_imset; apply: eq_bigl => i; rewrite inE.
move=> _ _ /imsetP [i _ ->] /imsetP [j _ ->].
apply: contraNT; rewrite -setI_eq0 => /set0Pn [/= s].
by rewrite !inE !mem_extset -!andbA => /and4P [/eqP -> _ /eqP -> _].
Qed.

Lemma card_adapt n (S : {set Sgn n}) : #|adapt S| = #|S|.
Proof.
elim: n => [//|n IHn] in S *.
rewrite (card_partition (partition_adapt S)).
rewrite (card_partition (partition_reext S)) !big_imset /=; last 2 first.
- move=> i j /=; rewrite !inE /= => Xii_neq0 Xij_neq0 eq_reext_ij.
  by apply/(@reext_inj _ _ S); rewrite ?inE.
- move=> i j /=; rewrite !inE /= => Xii_neq0 Xij_neq0.
  move=> /eqP; rewrite eq_extset -cards_eq0 IHn cards_eq0 Xij_neq0 /=.
  by move=> /andP [/eqP ? _].
apply: eq_bigr => i _; rewrite card_extset IHn card_imset //=.
by move=> s t /= /eqP; rewrite eq_extelt => /andP [_ /eqP].
Qed.

Lemma prop1084 n (S : {set Sgn n}) (a : Exp n) : a \in adapt S ->
  #|[set i | a i != 0%R]| <= trunc_log 2 #|S|.
Proof.
move=> a_adapt; apply: trunc_log_max => //.
pose B := [set b : Exp n | [forall i, (b i != 0%R) ==> (b i == a i)]].
apply: (@leq_trans #|B|) => [{a_adapt}|]; last first.
  rewrite -(card_adapt S) subset_leq_card //; apply/subsetP => b.
  rewrite in_set => /forallP bP; apply: adapt_down_closed a_adapt => i.
  by have := bP i; rewrite implyNb => /orP [/eqP ->|/eqP ->].
suff -> : B = [set [ffun i => if i \in (I : {set _}) then a i else 0%R]
              | I in powerset [set i | a i != 0%R]].
  rewrite card_in_imset; first by rewrite card_powerset leqnn.
  move=> I J /=; rewrite !in_set => PI PJ eqIJ; apply/setP => i.
  have := congr1 (fun f : {ffun _ -> _} => f i == 0%R) eqIJ; rewrite !ffunE.
  have [] := (subsetP PI i, subsetP PJ i); rewrite in_set.
  case: (i \in I) => [/(_ isT) /negPf ->|_];
  by case: (i \in J) => // /(_ isT) /negPf ->.
apply/setP => b; rewrite in_set.
apply/'forall_implyP/imsetP => [bP|[I]]; last first.
  by rewrite powersetE => /subsetP IP -> i; rewrite !ffunE; case: ifP.
exists [set i | b i != 0%R].
  rewrite powersetE; apply/subsetP => i; rewrite !in_set => b_neq0.
  by rewrite -(eqP (bP _ _)).
apply/ffunP => i; rewrite ffunE in_set.
by case: ifPn => [/bP /eqP <- //|]; rewrite negbK => /eqP.
Qed.

Lemma adapt_adapted n (S : {set Sgn n}) : adapted S (adapt S).
Proof.
rewrite /adapted {1}card_adapt eqxx /=.
elim: n => [|n IHn] in S *.
  apply/row_freeP; exists 1%:M; apply/matrixP=> i j.
  rewrite ?mulmx1 !mxE /mat_coef big_ord0.
  have := subset_leq_card (subsetT S); rewrite ?cardsT card_ffun !card_ord.
  by case: #|S| i j; do ![case=> //|move=>?].
have [->|SN0] := eqVneq S set0.
  move: (mat _ _); rewrite adaptn0 cards0 => A.
  by rewrite row_free_unit unitmxE det_mx00 unitr1.
have /set0Pn [/= s s_in] := SN0.
have /set0Pn [/= a a_in] : adapt S != set0 by rewrite adapt_eq0.
apply/inj_row_free => L LN0.
apply/rowP => j; rewrite mxE -(enum_valK_in s_in j).
move: (enum_val j) (enum_valP j) => /= t t_in {j}.
pose F t := L 0%R (enum_rank_in s_in t); rewrite /= in F; rewrite -/(F _).
pose r := #|exts S (restrict t)|.
move: r (leqnn r :  #|exts S (restrict t)| <= r) => r.
elim: r => [|/= r IHr] in t t_in *.
  by rewrite leqn0 cards_eq0 (negPf (exts_restrict_neq0 _)).
rewrite leq_eqVlt => /predU1P [extrt|]; last exact: IHr.
suff: \row_(j < #|exts S (restrict t)|)
       F (extelt (enum_val j) (restrict t)) == 0%R.
  move=> /eqP /rowP /(_ (enum_rank_in (ord0_in_exts t_in) (t 0%R))).
  by rewrite !mxE ?enum_rankK_in ?ord0_in_exts ?extE.
have /row_free_inj /raddf_eq0 /= <- := row_free_mat1 (exts S (restrict t)).
apply/eqP/rowP => /= j; rewrite !mxE /=.
rewrite (reindex_enum _ (ord0_in_exts t_in)) /= -/t.
rewrite (eq_bigr (fun x => F (extelt x (restrict t)) * M x (inord j))%R);
  last by move=> x x_in; rewrite !mxE ?enum_rankK_in //= /tmp.
pose G i t' := (\sum_(x in exts S t') F (extelt x t') * M x i)%R.
rewrite /= in G *; rewrite -/(G _ _).
have rt : restrict t \in Xi r.+1 S by rewrite inE extrt.
suff : \row_(r < #|Xi r.+1 S|) G (inord j) (enum_val r) == 0%R.
  move=> /eqP /rowP /(_ (enum_rank_in rt (restrict t))).
  by rewrite !mxE ?enum_rankK_in //.
have /row_free_inj /raddf_eq0 /= <- := IHn (Xi r.+1 S).
apply/eqP/rowP => l; rewrite !mxE (reindex_enum _ rt) /=.
evar (tmp : X ^ n -> rat); rewrite (eq_bigr tmp); last first.
  by move=> x x_in; rewrite !mxE ?enum_rankK_in //= mulr_suml /tmp.
rewrite /tmp {tmp} /G /=; set f := BIG_F.
transitivity (\sum_(i in Xi 1 S) f i)%R.
  symmetry; rewrite (big_setID (Xi r.+1 S)) /= (setIidPr _) ?leq_Xi //.
  rewrite [X in (_ + X)%R]big1 ?addr0 // => u.
  rewrite !inE -leqNgt => /andP [u_small _].
  by rewrite /f big1 // => x; rewrite inE => ?; rewrite IHr ?mul0r //= exteltK.
rewrite pair_big_dep (reindex (fun a => (restrict a, a 0%R))); last first.
  by exists (fun p => extelt p.2 p.1); move=> [??] /=; rewrite ?extE.
have /= := congr1 (fun X : 'M__ => X 0%R
  (enum_rank_in a_in (extelt (inord j) (enum_val l)))) LN0.
rewrite !mxE (reindex_enum _ s_in) /= => LN0_eq0.
rewrite -[RHS]LN0_eq0; symmetry; apply: eq_big => [u|u uS].
  rewrite [_ \in exts _ _]inE restrictK andbC.
  by have [/restrict_inW|//] := boolP (u \in S).
rewrite !mxE ?extE ?enum_rankK_in /F ?mat_coefS ?extE ?mulrA // extelt_in.
move: (enum_val l) (enum_valP l) => /= b b_in; rewrite inE in_adapt ?extE.
apply: subsetP b_in; rewrite subset_adapt // leq_Xi // inordK //= -?extrt //.
by rewrite (leq_trans (ltn_ord j)) ?exts_leq.
Qed.

End AbstractSigndet.

Section Signdet3.

Implicit Types (k : 'I_3).

Definition sign k : rat := if k >= 2 then -1%R else k%:Q.
Definition ctmat3   := \matrix_(i < 3, j < 3) sign i ^+ j.
Definition ctmat2 k := \matrix_(i < 2, j < 2) sign (lift k i) ^+ j.

Lemma det_ctmat2 k : \det (ctmat2 k) =
  if k <= 0 then - 2%:Q else if k > 1 then 1%R else - 1%R.
Proof.
case: k => [[|[|[|?]]] ?] //=;
rewrite (expand_det_col _ 0%R) !big_ord_recl big_ord0;
rewrite /cofactor ?det_mx11 !mxE /sign //=;
by rewrite ?(mul0r, expr0, expr1, mul1r, addr0, add0r).
Qed.

Lemma det_ctmat3 : \det ctmat3 = 2%:Q.
Proof.
rewrite (expand_det_col _ ord_max).
transitivity (\sum_i ctmat3 i ord_max * ((-1) ^+ i * \det (ctmat2 i)))%R;
  last by rewrite !big_ord_recl big_ord0 !mxE !det_ctmat2.
apply: eq_bigr => i _; congr (_ * (_ *  _))%R; last congr (\det _).
  by rewrite -signr_odd odd_add addbF signr_odd.
by apply/matrixP => /= k l; rewrite !mxE //=; case: l => [[|[|?]] ?].
Qed.

Lemma row_free_ctmat1 (S : {set 'I_3}) : row_free (mat1 ctmat3 S).
Proof.
pose M S := \matrix_(i < #|S|, j < #|S|) sign (enum_val i) ^+ j.
have := subset_leq_card (subsetT S); rewrite cardsT card_ord => cardS.
have -> : mat1 ctmat3 S = M _.
  apply/matrixP => i j; rewrite !mxE inordK -?enum_val_nth //.
  by rewrite (leq_trans (ltn_ord _)).
move: cardS; have enumI3E : enum 'I_3 = [seq inord i | i <- iota 0 3].
  apply: (@eq_from_nth _ 0%R).
    by rewrite -cardE card_ord size_map size_iota.
  move=> i; rewrite -cardE card_ord => i_small.
  rewrite -{1}[i](@inordK 2) // nth_ord_enum (nth_map 0) //=.
  by case: i i_small => [|[|[|?]]].
do 3?[rewrite leq_eqVlt orbC => /orP []; rewrite ?ltnS ?leqn0].
- rewrite cards_eq0 => /eqP ->; rewrite row_free_unit unitmxE.
  by move: (M _); rewrite cards0 => M'; rewrite det_mx00.
- move=> /cards1P [/= x ->].
  suff -> : M [set x] = 1%:M by apply/inj_row_free => v; rewrite mulmx1.
  apply/matrixP => i j; rewrite !mxE.
  have := enum_valP i; rewrite inE => /eqP ->.
  by move: i j => /=; rewrite cards1 => i j; rewrite !ord1 expr0 eqxx.
- move=> /eqP S2; have /cards1P [x /(congr1 (@setC _))] : #|~: S| == 1.
    by rewrite cardsCs card_ord setCK S2.
  rewrite setCK => S_def; rewrite S_def in S2 *.
  rewrite row_free_unit unitmxE unitfE.
  suff: M [set~ x] = castmx (esym S2, esym S2) (ctmat2 x).
    case: _ / (esym S2) (M _) => A ->; rewrite castmx_id.
    by rewrite det_ctmat2 {S_def S2}; case: x => [[|[|?]] ?].
  apply/matrixP=> i j; rewrite !(mxE, castmxE) ?esymK /=.
  congr (sign _ ^+ _); apply/val_inj => /=.
  rewrite /enum_val -filter_index_enum /index_enum -enumT /= enumI3E.
  have : i < 2 by rewrite (leq_trans (ltn_ord i)) ?S2.
  case: x i {j S2 S_def} => [[|[|[|?]]] ?] [[|[|[|?]]] ?] //=;
  by rewrite !topredE ?inE -!val_eqE /= !inordK //=.
- move=> /eqP S3; have /= S_def : S = setT.
    by apply/eqP; rewrite eqEcard ?subsetT ?cardsT ?card_ord S3.
  rewrite row_free_unit unitmxE unitfE; rewrite S_def in S3 *.
  suff: M setT = castmx (esym S3, esym S3) ctmat3.
    by case: _ / (esym S3) (M _) => A ->; rewrite castmx_id det_ctmat3.
  apply/matrixP => i j; rewrite !(mxE, castmxE) ?esymK /=.
  congr (sign _ ^+ _); apply/val_inj => /=.
  rewrite /enum_val enum_setT -enumT /= enumI3E /=.
  have : i < 3 by rewrite (leq_trans (ltn_ord i)) ?cardsT ?card_ord.
  by case: (val i) => [|[|[|?]]]; rewrite ?inordK //=.
Qed.

Theorem ctmat_adapted n (S : {set 'I_3 ^ n}) : adapted ctmat3 S (adapt S).
Proof. exact/adapt_adapted/row_free_ctmat1. Qed.

End Signdet3.

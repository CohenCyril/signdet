From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path fintype finset finfun div bigop prime tuple.
From mathcomp Require Import perm zmodp ssralg poly polydiv order ssrnum ssrint.
From mathcomp Require Import rat matrix mxalgebra binomial path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def Pdiv.Ring Pdiv.ComRing.
Local Open Scope nat_scope.

Section extrassr.

Local Open Scope ring_scope.

Lemma mulrIb (R : zmodType) (x : R) : x != 0 ->
   injective (fun b : bool => x *+ b).
Proof. by move=> /negPf x0F [] [] //= /eqP; rewrite ?x0F // eq_sym x0F. Qed.

Lemma inj_row_free (F : fieldType) (n p : nat) (A : 'M[F]_(n, p)) :
  (forall v : 'rV_n, v *m A = 0 -> v = 0) -> row_free A.
Proof.
move=> Ainj; rewrite -kermx_eq0; apply/eqP.
apply/row_matrixP => i; rewrite row0; apply/Ainj.
by rewrite -row_mul mulmx_ker row0.
Qed.

Lemma det_mx11 (R : comRingType) (M : 'M[R]_1) : \det M = M 0 0.
Proof. by rewrite {1}[M]mx11_scalar det_scalar. Qed.

End extrassr.

Section Ext.

Variables (n : nat) (X : finType).
Implicit Types (S : {set X ^ n.+1}) (R : {set X ^ n}).
Implicit Types (s : X ^ n.+1) (r : X ^ n) (x y : X) (m : nat).

(* Extension of s with one element x at the begining *)
Definition ext x r : X ^ n.+1 := [ffun i => oapp r x (unlift 0%R i)].

(* Restriction of b, without the last element, the inverse of ext *)
Definition rem s : X ^ n := [ffun i => s (lift 0%R i)].

(* extension of a set with one element x at the begining. *)
Definition extset x R : {set X ^ n.+1} := [set ext x s | s in R].

(* the set of possible completions of r by x in S *)
Definition compl S r : {set X} := [set x | ext x r \in S].

(* the set of elements with at least m + 1 extensions in S *)
Definition Xi m S : {set X ^ n} := [set r : X ^ n | m < #|compl S r|].

Lemma remK s : ext (s 0%R) (rem s) = s.
Proof.
by apply/ffunP=> i; rewrite ffunE; case: unliftP => [j|] ->; rewrite //= ffunE.
Qed.

Lemma extK x : cancel (ext x) rem.
Proof. by move=> b; apply/ffunP=> i; rewrite !ffunE liftK. Qed.

Lemma ext0 x r : ext x r 0%R = x.
Proof. by rewrite /ext ffunE unlift_none. Qed.

Let extE' := (inE, ext0, extK, remK, eqxx).

Lemma eq_ext x x' (r r' : X ^ n) :
  (ext x r == ext x' r') = (x == x') && (r == r').
Proof.
have [->|] /= := altP (x =P x'); first by rewrite (can_eq (@extK _)).
by apply: contraNF => /eqP/ffunP/(_ 0%R); rewrite !ext0 => ->.
Qed.

Lemma compl0 r : compl set0 r = set0.
Proof. by apply/setP=> i; rewrite !inE. Qed.

Lemma compl_rem_neq0 S s : s \in S -> compl S (rem s) != set0.
Proof.
move=> sS; have : s 0%R \in compl S (rem s) by rewrite !extE'.
by apply: contraTneq => ->; rewrite inE.
Qed.

Lemma ext_in S r x : (ext x r \in S) = (x \in compl S r).
Proof. by rewrite inE. Qed.

Lemma card_extset R x : #|extset x R| = #|R|.
Proof.
by rewrite card_imset // => u v /eqP; rewrite eq_ext => /andP [_ /eqP].
Qed.

Lemma mem_extset x s R : s \in extset x R = (s 0%R == x) && (rem s \in R).
Proof.
apply/imsetP/idP => [[r rS ->]|/andP [/eqP<-] rsS]; first by rewrite !extE'.
by exists (rem s) => //; rewrite !extE'.
Qed.

Lemma mem_extset_r x r R : ext x r \in extset x R = (r \in R).
Proof. by rewrite mem_extset ?extE'. Qed.

Lemma rem_inW S s : s \in S -> rem s \in Xi 0 S.
Proof.
by move=> sS; rewrite inE; apply/card_gt0P; exists (s 0%R); rewrite !extE'.
Qed.

Lemma extset0 x : extset x set0 = set0.
Proof. by rewrite /extset imset0. Qed.

Lemma extsetK x : cancel (extset x) (Xi 0).
Proof.
move=> S; apply/setP => /= s; apply/idP/idP => [|sS]; last first.
  by rewrite -[s](extK x) rem_inW // mem_extset_r.
by rewrite inE => /card_gt0P [y]; rewrite inE mem_extset ?extE' => /andP [].
Qed.

Definition extE := (extE', mem_extset, extsetK, extset0).

Fact ord0_in_compl S s : s \in S -> s 0%R \in compl S (rem s).
Proof. by rewrite !extE'. Qed.

Lemma subset_extset x : {mono extset x : R R' / R \subset R'}.
Proof.
move=> R R'; apply/subsetP/subsetP => RR' /= r.
  by move/(mem_imset (ext x))/RR'; rewrite mem_extset_r.
by case/imsetP=> r' rR ->; rewrite mem_extset_r RR'.
Qed.

Lemma subset_compl r : {homo compl^~ r : S S' / S \subset S'}.
Proof. by move=> ???; apply/subsetP=> x; rewrite !inE; apply/subsetP. Qed.

Lemma subset_Xi m : {homo Xi m : S S' / S \subset S'}.
Proof.
move=> S S' subSS'; apply/subsetP=> s; rewrite !in_set => /leq_trans-> //.
exact/subset_leq_card/subset_compl.
Qed.

Lemma leq_Xi S : {homo Xi^~ S : m p / p <= m >-> m \subset p}.
Proof. by move=> m p ?; apply/subsetP => s; rewrite !inE; apply/leq_trans. Qed.

Lemma Xi0 i : Xi i set0 = set0.
Proof. by apply/setP => e; rewrite !inE compl0 cards0. Qed.

Lemma Xi1_eq0 S : (Xi 0 S == set0) = (S == set0).
Proof.
apply/idP/idP=> [|/eqP->]; last by rewrite Xi0.
apply: contraTT => /set0Pn [x xS].
by apply/set0Pn; exists (rem x); apply: rem_inW.
Qed.

End Ext.

Local Open Scope ring_scope.

Section AbstractSigndet.

Variables (F : fieldType) (k' : nat).
Let k := k'.+1.
Let X := 'I_k.
Variable M : 'M[F]_k.

Definition mat1 (S : {set X}) : 'M[F]_#|S| :=
  \matrix_(i, j) M (enum_val i) (inord j).

Hypothesis row_free_mat1 : forall (S : {set X}), row_free (mat1 S).

Definition mat_coef n (i : X ^ n) (j : X ^ n) := \prod_k M (i k) (j k).

Definition mat n (S : {set X ^ n}) (A : {set X ^ n}) : 'M_(#|S|, #|A|) :=
  \matrix_(i < #|S|, j < #|A|) mat_coef (enum_val i) (enum_val j).

Definition adapted n (S : {set X ^ n}) (A : {set X ^ n}) :=
  (#|A| == #|S|) && row_free (mat S A).

Fixpoint adapt n : {set X ^ n} -> {set X ^ n} :=
  if n isn't _.+1 then id
  else fun S => \bigcup_(i < k) extset i (adapt (Xi i S)).

Arguments adapt n S : simpl never.

Lemma adapt0 (S : {set X^0}) : adapt S = S. Proof. by []. Qed.

Lemma adaptS n (S : {set X ^ n.+1}) :
  adapt S = \bigcup_(i < k) extset i (adapt (Xi i S)).
Proof. by []. Qed.

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
apply/set0Pn; exists (ext ord0 x).
by apply/bigcupP; exists 0 => //; rewrite ?extE.
Qed.

Lemma subset_adapt n : {homo @adapt n : S S' / S \subset S'}.
Proof.
elim: n => [//|n IHn] S S' subSS' /=; apply/bigcupsP => i _.
by rewrite (bigcup_max i) // subset_extset IHn // subset_Xi.
Qed.

Lemma in_adapt n (S : {set X ^ n.+1}) (a : X ^ n.+1) :
  (a \in adapt S) = (rem a \in adapt (Xi (a 0) S)).
Proof.
move=> /=; apply/bigcupP/idP => [[i _ /imsetP [s sAXi ->]]|].
  by rewrite ?extE.
by move=> ra; exists (a 0); rewrite ?extE.
Qed.

Lemma adapt_down_closed  n (S : {set X ^ n}) (a b : X ^ n) :
  (forall i, b i <= a i)%N -> a \in adapt S -> b \in adapt S.
Proof.
elim: n => [|/= n IHn] in S a b *.
  by move=> _; rewrite (fintype_le1P _ b)// card_ffun !card_ord.
move=> leq_ba; rewrite !in_adapt => raAXi.
have: rem b \in adapt (Xi (a 0) S).
  by apply: IHn raAXi => i; rewrite !ffunE leq_ba.
by apply: subsetP; rewrite subset_adapt ?leq_Xi ?ltnS ?leq_ba.
Qed.

Lemma mat_coefS n (s : X ^ n.+1) (a : X ^ n.+1) :
  mat_coef s a = M (s 0) (a 0) * mat_coef (rem s) (rem a).
Proof.
rewrite [LHS]big_ord_recl; congr (_ * _).
by apply: eq_bigr => i _; rewrite !ffunE.
Qed.

Theorem mat_adapt_free n (S : {set X ^ n}) : row_free (mat S (adapt S)).
Proof.
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
pose l t := L 0 (enum_rank_in s_in t); rewrite /= in l; rewrite -/(l _).
have [r] := ubnPleq #|compl S (rem t)|; elim: r => [|r IHr] in t t_in *.
  by rewrite leqn0 cards_eq0 (negPf (compl_rem_neq0 _)).
rewrite leq_eqVlt => /predU1P [extrt|]; last exact: IHr.
suff: \row_(j < #|compl S (rem t)|)
       l (ext (enum_val j) (rem t)) == 0.
  move=> /eqP /rowP /(_ (enum_rank_in (ord0_in_compl t_in) (t 0))).
  by rewrite !mxE ?enum_rankK_in ?ord0_in_compl ?extE.
have /(@row_free_inj _ 1) := row_free_mat1 (compl S (rem t)).
rewrite -[mulmx^~ _]/(mulmxr _) => /raddf_eq0 <-.
apply/eqP/rowP => /= j; rewrite !mxE /=.
rewrite (big_enum_rank (ord0_in_compl t_in)) /= -/t.
rewrite (eq_bigr (fun x => l (ext x (rem t)) * M x (inord j)));
  last by move=> x x_in; rewrite !mxE ?enum_rankK_in //= /tmp.
pose G i t' := (\sum_(x in compl S t') l (ext x t') * M x i).
rewrite /= in G *; rewrite -/(G _ _).
have rt : rem t \in Xi r S by rewrite inE extrt.
suff : \row_(p < #|Xi r S|) G (inord j) (enum_val p) == 0.
  move=> /eqP /rowP /(_ (enum_rank_in rt (rem t))).
  by rewrite !mxE ?enum_rankK_in //.
have /(@row_free_inj _ 1) := IHn (Xi r S).
rewrite -[mulmx^~ _]/(mulmxr _) => /raddf_eq0 /= <-.
apply/eqP/rowP => m; rewrite !mxE (big_enum_rank rt) /=.
under eq_bigr => x x_in do rewrite !mxE ?enum_rankK_in //= mulr_suml.
set f := BIG_F; transitivity (\sum_(i in Xi 0 S) f i).
  symmetry; rewrite (big_setID (Xi r S)) /= (setIidPr _) ?leq_Xi //.
  rewrite [X in (_ + X)]big1 ?addr0 // => u.
  rewrite !inE -leqNgt => /andP [u_small _].
  by rewrite /f big1 // => x; rewrite inE => ?; rewrite IHr ?mul0r //= extK.
rewrite pair_big_dep (reindex (fun a => (rem a, a 0))) /=; last first.
  by exists (fun p => ext p.2 p.1) => [x|[//? ?]]; rewrite !inE !extE.
have /matrixP/(_ 0 (enum_rank_in a_in (ext (inord j) (enum_val m)))) := LN0.
rewrite !mxE (big_enum_rank s_in) /= => LN0_eq0.
rewrite -[RHS]LN0_eq0; symmetry; apply: eq_big => [u|u uS].
  rewrite [_ \in compl _ _]inE remK andbC.
  by have [/rem_inW|//] := boolP (u \in S).
rewrite !mxE ?extE ?enum_rankK_in /l ?mat_coefS ?extE ?mulrA // ext_in.
move: (enum_val m) (enum_valP m) => /= b b_in; rewrite inE in_adapt ?extE.
apply: subsetP b_in; rewrite subset_adapt // leq_Xi // -ltnS inordK -?extrt //.
by rewrite (leq_trans (leq_trans (ltn_ord _) (max_card _))) ?card_ord.
Qed.

Lemma card_adapt n (S : {set X ^ n}) : #|adapt S| = #|S|.
Proof.
apply/eqP; rewrite eqn_leq andbC; have := mat_adapt_free S.
rewrite -row_leq_rank => /leq_trans->/=; last by rewrite rank_leq_col.
elim: n => // n IHn in S *; rewrite adaptS /=.
rewrite (@leq_trans (\sum_(i < k) #|Xi i S|))//=.
  elim/big_rec2: _; rewrite ?cards0// => i m A _ A_le.
  by rewrite cardsU (leq_trans (leq_subr _ _))// card_extset leq_add.
under eq_bigr do rewrite -sum1dep_card big_mkcond/=; rewrite exchange_big /=.
rewrite (eq_bigr (fun r => \sum_x (ext x r \in S))%N) => [|r]; last first.
  rewrite -big_mkcond/= big_ord_narrow 1?(leq_trans (max_card _)) ?card_ord//.
  by rewrite sum1_card card_ord -sum1dep_card big_mkcond.
rewrite exchange_big pair_big -big_mkcond/=. 
rewrite -(@reindex _ _ _ _ _ (fun p => ext p.1 p.2) _ (fun=> _)) ?sum1_card//.
by exists (fun s : X ^ _ => (s 0, rem s)) => [[? ?]|x]; rewrite ?extE.
Qed.

Lemma adapt_adapted n (S : {set X ^ n}) : adapted S (adapt S).
Proof. by rewrite /adapted mat_adapt_free card_adapt eqxx. Qed.

Proposition prop_10_84 n (S : {set X ^ n}) (a : X ^ n) : a \in adapt S ->
  (#|[set i | a i != 0%R]| <= trunc_log 2 #|S|)%N.
Proof.
pose I (a : X ^ n) : {set 'I_n} := [set i | a i != 0]; rewrite -/(I _).
move=> a_adapt; apply: trunc_log_max => //.
pose nullify (B : {set 'I_n}) : X ^ n := [ffun i => a i *+ (i \in B)].
suff -> : (2 ^ #|I a| = #|nullify @: powerset (I a)|)%N.
  rewrite -[#|S|]card_adapt subset_leq_card //; apply/subsetP => b.
  move=> /imsetP [/= J]; rewrite inE => /subsetP JsubI -> {b}.
  by apply: adapt_down_closed a_adapt => /= i; rewrite ffunE; case: (_ \in _).
rewrite card_in_imset ?card_powerset // => J1 J2.
rewrite !inE => /subsetP J1a /subsetP J2a eqJ; apply/setP => i.
have [iI|/norP [/negPf-> /negPf->] //] := boolP ((i \in J1) || (i \in J2)).
have /mulrIb : a i != 0 by move: iI => /orP [/J1a|/J2a]; rewrite inE.
by apply; have /ffunP/(_ i) := eqJ; rewrite !ffunE.
Qed.

End AbstractSigndet.

Section Signdet3.

Implicit Type (k : 'I_3).

Definition sign k : rat := if (k >= 2)%N then -1 else k%:Q.
Definition ctmat3   := \matrix_(i < 3, j < 3) sign i ^ j.
Definition ctmat2 k := \matrix_(i < 2, j < 2) sign (lift k i) ^ j.

Lemma det_ctmat2 k : \det (ctmat2 k) =
  if (k <= 0)%N then - 2%:Q else if (k > 1)%N then 1 else -1.
Proof.
by case: k => [[|[|[|?]]] ?] //=;
   rewrite (expand_det_col _ 0) !big_ord_recl big_ord0;
   rewrite /cofactor ?det_mx11 !mxE /sign //=;
   rewrite ?(mul0r, expr0, expr1, mul1r, addr0, add0r).
Qed.

Lemma det_ctmat3 : \det ctmat3 = 2%:Q.
Proof.
rewrite (expand_det_col _ ord_max).
transitivity (\sum_i ctmat3 i ord_max * ((-1) ^+ i * \det (ctmat2 i)));
  last by rewrite !big_ord_recl big_ord0 !mxE !det_ctmat2.
apply: eq_bigr => i _; congr (_ * (_ *  _)); last congr (\det _).
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
  apply: (@eq_from_nth _ 0).
    by rewrite -cardE card_ord size_map size_iota.
  move=> i; rewrite -cardE card_ord => i_small.
  rewrite -{1}[i](@inordK 2) // nth_ord_enum (nth_map 0%N) //=.
  by case: i i_small => [|[|[|?]]].
do 3?[rewrite leq_eqVlt orbC => /orP []; rewrite ?ltnS ?leqn0].
- rewrite cards_eq0 => /eqP ->; rewrite row_free_unit unitmxE.
  by move: (M _); rewrite cards0 => M'; rewrite det_mx00.
- move=> /cards1P [/= x ->].
  suff -> : M [set x] = 1%:M by apply/inj_row_free => v; rewrite mulmx1.
  apply/matrixP => i j; rewrite !mxE.
  have := enum_valP i; rewrite inE => /eqP ->.
  by move: i j => /=; rewrite cards1 => i j; rewrite !ord1 expr0 eqxx.
- move=> /eqP S2; have /cards1P [x /(congr1 (@setC _))] : #|~: S| == 1%N.
    by rewrite cardsCs card_ord setCK S2.
  rewrite setCK => S_def; rewrite S_def in S2 *.
  rewrite row_free_unit unitmxE unitfE.
  suff: M [set~ x] = castmx (esym S2, esym S2) (ctmat2 x).
    case: _ / (esym S2) (M _) => A ->; rewrite castmx_id.
    by rewrite det_ctmat2 {S_def S2}; case: x => [[|[|?]] ?].
  apply/matrixP=> i j; rewrite !(mxE, castmxE) ?esymK /=; congr (sign _ ^+ _).
  apply/val_inj; rewrite /enum_val /=; move: i (enum_default _); rewrite S2.
  rewrite /enum_val -filter_index_enum /index_enum -enumT enumI3E /=.
  rewrite /= !topredE !inE -!val_eqE /= !inordK //=.
  by case: x {j S2 S_def} => [[|[|[|?]]] ?] [[|[|?]] ?] /=; rewrite ?inordK.
- move=> /eqP S3; have /= S_def : S = setT.
    by apply/eqP; rewrite eqEcard ?subsetT ?cardsT ?card_ord S3.
  rewrite row_free_unit unitmxE unitfE; rewrite S_def in S3 *.
  suff: M setT = castmx (esym S3, esym S3) ctmat3.
    by case: _ / (esym S3) (M _) => A ->; rewrite castmx_id det_ctmat3.
  apply/matrixP => i j; rewrite !(mxE, castmxE) ?esymK /=.
  congr (sign _ ^+ _); apply/val_inj => /=.
  rewrite /enum_val enum_setT -enumT /= enumI3E /=.
  have : (i < 3)%N by rewrite (leq_trans (ltn_ord i)) ?cardsT ?card_ord.
  by case: (val i) => [|[|[|?]]]; rewrite ?inordK //=.
Qed.

Theorem ctmat_adapted n (S : {set 'I_3 ^ n}) : adapted ctmat3 S (adapt S).
Proof. exact/adapt_adapted/row_free_ctmat1. Qed.

End Signdet3.

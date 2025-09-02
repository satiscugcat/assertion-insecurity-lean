import Mathlib

inductive EX {A: Type} (P: A -> Type): Type
| intro (w: A) (h: P w)

inductive TermVar
| cons : Nat -> TermVar
deriving DecidableEq

inductive KeyVar
| cons : Nat  -> KeyVar
deriving DecidableEq

inductive Name
| cons : Nat -> Name
deriving DecidableEq

inductive Var
| term (t: TermVar) 
| key (k:KeyVar)
deriving DecidableEq



inductive Key: Type
| priv (k: Name)
| pub (k: Name)
| var (v: KeyVar)
deriving DecidableEq

inductive Term: Type
| var (v: TermVar)
| name (m: Name)
| key (k: Key)
| pair (t1 t2: Term)
| enc (t: Term) (k: Key)
deriving DecidableEq

   
abbrev TermSet := Set Term

def var_to_term (v: Var) : Term :=
  match v with
  | Var.term v => Term.var v
  | Var.key v => Term.key (Key.var v)
 


def FVSetTerm : Term -> Set Var
| Term.var v => {Var.term v}
| Term.name _ => ∅ 
| Term.key (Key.var v) => {Var.key v}
| Term.key _ => ∅
| Term.pair t1 t2 =>  FVSetTerm t1 ∪ FVSetTerm t2
| Term.enc t' k => (FVSetTerm t') ∪
                           match k with 
                             | Key.var v => {Var.key v} 
                             | _ => ∅


      
inductive dy : TermSet -> Term -> Type
| ax {X: TermSet} {t: Term} (inH:  t ∈ X) : dy X t
| pk {X: TermSet} {k: Name} (kH: dy X (Term.key (Key.priv k)) ) : dy X (Term.key (Key.pub k))
                                                           
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dy X t1
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dy X t2
| pair {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dy X (Term.pair t1 t2)
                                                               
| sdec {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.priv k))) (kH: dy X (Term.key (Key.priv k))): dy X t
| senc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.priv k))) : dy X (Term.enc t (Key.priv k))
                                                                                     
| adec {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.pub k))) (kH: dy X (Term.key (Key.priv k))): dy X t
| aenc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.pub k))) : dy X (Term.enc t (Key.pub k))


inductive dyProperSubProof : ∀ {X₁ X₂ t₁ t₂}, dy X₁ t₁ -> dy X₂ t₂ -> Prop
| pk {X: TermSet} {k: Name} (kH: dy X (Term.key (Key.priv k))) : dyProperSubProof kH (dy.pk kH)                                                       
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dyProperSubProof splitH (dy.splitL splitH)
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dyProperSubProof splitH (dy.splitR splitH)
| pair_left {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dyProperSubProof tH (dy.pair tH uH)
| pair_right {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dyProperSubProof uH (dy.pair tH uH)
                                                               
| sdec_enc {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.priv k))) (kH: dy X (Term.key (Key.priv k))): dyProperSubProof encH (dy.sdec encH kH)
| sdec_key {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.priv k))) (kH: dy X (Term.key (Key.priv k))): dyProperSubProof kH (dy.sdec encH kH)

| senc_term {X: TermSet} {t: Term} {k: Name} (tH: dy X t) {kH: dy X (Term.key (Key.priv k))} : dyProperSubProof tH (dy.senc tH kH)
| senc_key {X: TermSet} {t: Term} {k: Name} {tH: dy X t} (kH: dy X (Term.key (Key.priv k))) : dyProperSubProof kH (dy.senc tH kH)

| adec_enc {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.pub k))) (kH: dy X (Term.key (Key.priv k))): dyProperSubProof encH (dy.adec encH kH)
| adec_key {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.pub k))) (kH: dy X (Term.key (Key.priv k))): dyProperSubProof kH (dy.adec encH kH)                                                                                     
| aenc_term {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.pub k))) : dyProperSubProof tH (dy.aenc tH kH)
| aenc_key {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.pub k))) : dyProperSubProof kH (dy.aenc tH kH)

| trans_pk {X: TermSet} {k: Name} {kH: dy X (Term.key (Key.priv k))} {X' tp} {p: dy X' tp} (sub: dyProperSubProof p kH): dyProperSubProof p (dy.pk kH)                                                       
| trans_splitL {X: TermSet} {t1 t2: Term} {splitH: dy X (Term.pair t1 t2)} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p splitH) : dyProperSubProof p (dy.splitL splitH)
| trans_splitR {X: TermSet} {t1 t2: Term} {splitH: dy X (Term.pair t1 t2)} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p splitH): dyProperSubProof p (dy.splitR splitH)
| trans_pair_left {X: TermSet} {t1 t2: Term} {tH: dy X t1} {uH: dy X t2} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p tH): dyProperSubProof p (dy.pair tH uH)
| trans_pair_right {X: TermSet} {t1 t2: Term} {tH: dy X t1} {uH: dy X t2} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p uH): dyProperSubProof p (dy.pair tH uH)
                                                               
| trans_sdec_enc {X: TermSet} {t: Term} {k: Name} {encH: dy X (Term.enc t (Key.priv k))} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p encH): dyProperSubProof p (dy.sdec encH kH)
| trans_sdec_key {X: TermSet} {t: Term} {k: Name} {encH: dy X (Term.enc t (Key.priv k))} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p kH): dyProperSubProof p (dy.sdec encH kH)

| trans_senc_term {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p tH): dyProperSubProof p (dy.senc tH kH)
| trans_senc_key {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p kH) : dyProperSubProof p (dy.senc tH kH)

| trans_adec_enc {X: TermSet} {t: Term} {k: Name} {encH: dy X (Term.enc t (Key.pub k))} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p encH): dyProperSubProof p (dy.adec encH kH)
| trans_adec_key {X: TermSet} {t: Term} {k: Name} {encH: dy X (Term.enc t (Key.pub k))} {kH: dy X (Term.key (Key.priv k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p kH): dyProperSubProof p (dy.adec encH kH)                                                                                     
| trans_aenc_term {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.pub k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p tH) : dyProperSubProof p (dy.aenc tH kH)
| trans_aenc_key {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.pub k))} {tp X'} {p: dy X' tp} (sub: dyProperSubProof p kH): dyProperSubProof p (dy.aenc tH kH)

theorem dySubProofTrans : ∀ {X₁ t₁ X₂ t₂ X₃ t₃} {p₁: dy X₁ t₁} {p₂: dy X₂ t₂} {p₃: dy X₃ t₃}, dyProperSubProof p₁ p₂ -> dyProperSubProof p₂ p₃ -> dyProperSubProof p₁ p₃ :=
  by
    intros _ _ _ _ _ _ p₁ p₂ p₃
    intros sub₁ sub₂
    induction sub₂ with
    | pk kH =>
      constructor
      exact sub₁
    | splitL splitH =>
      apply dyProperSubProof.trans_splitL
      exact sub₁
    | splitR splitH =>
      apply dyProperSubProof.trans_splitR
      exact sub₁
    | pair_left tH uH => 
      apply dyProperSubProof.trans_pair_left
      exact sub₁
    | pair_right =>
      apply dyProperSubProof.trans_pair_right
      exact sub₁
    | sdec_enc =>
      apply dyProperSubProof.trans_sdec_enc
      exact sub₁
    | sdec_key =>
      apply dyProperSubProof.trans_sdec_key
      exact sub₁
    | adec_enc =>
      apply dyProperSubProof.trans_adec_enc
      exact sub₁
    | adec_key =>
      apply dyProperSubProof.trans_adec_key
      exact sub₁
    | senc_term =>
      constructor
      exact sub₁
    | senc_key =>
      apply dyProperSubProof.trans_senc_key
      exact sub₁
    | aenc_term =>
      constructor
      exact sub₁
    | aenc_key =>
      apply dyProperSubProof.trans_aenc_key
      exact sub₁
    
    | trans_pk sub sub_ih =>
      apply dyProperSubProof.trans_pk
      apply sub_ih
      exact sub₁

    | trans_splitL sub sub_ih =>
      apply dyProperSubProof.trans_splitL
      apply sub_ih
      exact sub₁
    | trans_splitR sub sub_ih =>
      apply dyProperSubProof.trans_splitR
      apply sub_ih
      exact sub₁
    | trans_pair_left sub sub_ih => 
      apply dyProperSubProof.trans_pair_left
      apply sub_ih
      exact sub₁
    | trans_pair_right sub sub_ih =>
      apply dyProperSubProof.trans_pair_right
      apply sub_ih
      exact sub₁
    | trans_sdec_enc sub sub_ih =>
      apply dyProperSubProof.trans_sdec_enc
      apply sub_ih
      exact sub₁
    | trans_sdec_key sub sub_ih =>
      apply dyProperSubProof.trans_sdec_key
      apply sub_ih
      exact sub₁
    | trans_adec_enc sub sub_ih =>
      apply dyProperSubProof.trans_adec_enc
      apply sub_ih
      exact sub₁
    | trans_adec_key sub sub_ih =>
      apply dyProperSubProof.trans_adec_key
      apply sub_ih
      exact sub₁
    | trans_senc_term sub sub_ih =>
      constructor
      apply sub_ih
      exact sub₁
    | trans_senc_key sub sub_ih =>
      apply dyProperSubProof.trans_senc_key
      apply sub_ih
      exact sub₁
    | trans_aenc_term sub sub_ih =>
      constructor
      apply sub_ih
      exact sub₁
    | trans_aenc_key sub sub_ih  =>
      apply dyProperSubProof.trans_aenc_key
      apply sub_ih
      exact sub₁
 
    
      
    
theorem dyStrongInduction : ∀ {P: ∀ {X t}, dy X t → Prop}, 
        (∀ {X} {t} (p: dy X t), ( ∀ {X'} {t'} (p': dy X' t'), dyProperSubProof p' p → P p' ) → P p) → 
        ∀ {X t} (p: dy X t), P p :=
        by
          intros P iH
          have Q : ∀ {X t} (p: dy X t), P p ∧ ∀ {X' t'} (p': dy X' t'), dyProperSubProof p' p → P p'
          {
            intros X t p
            induction p with
            | ax =>
              apply And.intro
              {
                apply iH
                intros _ _ _ a
                cases a
              }
              intros _ _ p' sub
              cases sub
            | pk kH kH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | pk => 
                  apply And.left kH_ih
                | trans_pk sub =>
                  apply And.right kH_ih
                  exact sub
              }
              {
                intros _ _ p' sub
                cases sub with
                | pk =>
                  apply And.left kH_ih
                
                | trans_pk sub =>
                  apply And.right kH_ih
                  exact sub
              }
            | splitL splitH splitH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | splitL => exact And.left splitH_ih
                | trans_splitL sub => 
                  apply And.right splitH_ih
                  exact sub
              }
              {
                
                intros X' t' p' sub
                cases sub with
                | splitL => exact And.left splitH_ih
                | trans_splitL sub => 
                  apply And.right splitH_ih
                  exact sub
              }
            | splitR splitH splitH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | splitR => exact And.left splitH_ih
                | trans_splitR sub => 
                  apply And.right splitH_ih
                  exact sub
              }
              {
                
                intros X' t' p' sub
                cases sub with
                | splitR => exact And.left splitH_ih
                | trans_splitR sub => 
                  apply And.right splitH_ih
                  exact sub
              }
            | pair tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | pair_left => exact And.left tH_ih
                | trans_pair_left sub => 
                  apply And.right tH_ih
                  exact sub
                | pair_right => exact And.left uH_ih
                | trans_pair_right sub => 
                  apply And.right uH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | pair_left => exact And.left tH_ih
                | trans_pair_left sub => 
                  apply And.right tH_ih
                  exact sub
                | pair_right => exact And.left uH_ih
                | trans_pair_right sub => 
                  apply And.right uH_ih
                  exact sub
              }

            | sdec tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | sdec_key => exact And.left uH_ih
                | trans_sdec_key sub => 
                  apply And.right uH_ih
                  exact sub
                | sdec_enc => exact And.left tH_ih
                | trans_sdec_enc sub => 
                  apply And.right tH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | sdec_key => exact And.left uH_ih
                | trans_sdec_key sub => 
                  apply And.right uH_ih
                  exact sub
                | sdec_enc => exact And.left tH_ih
                | trans_sdec_enc sub => 
                  apply And.right tH_ih
                  exact sub
              }

            | senc tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | senc_key => exact And.left uH_ih
                | trans_senc_key sub => 
                  apply And.right uH_ih
                  exact sub
                | senc_term => exact And.left tH_ih
                | trans_senc_term sub => 
                  apply And.right tH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | senc_key => exact And.left uH_ih
                | trans_senc_key sub => 
                  apply And.right uH_ih
                  exact sub
                | senc_term => exact And.left tH_ih
                | trans_senc_term sub => 
                  apply And.right tH_ih
                  exact sub
              }

              | adec tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | adec_key => exact And.left uH_ih
                | trans_adec_key sub => 
                  apply And.right uH_ih
                  exact sub
                | adec_enc => exact And.left tH_ih
                | trans_adec_enc sub => 
                  apply And.right tH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | adec_key => exact And.left uH_ih
                | trans_adec_key sub => 
                  apply And.right uH_ih
                  exact sub
                | adec_enc => exact And.left tH_ih
                | trans_adec_enc sub => 
                  apply And.right tH_ih
                  exact sub
              }

            | aenc tH uH tH_ih uH_ih =>
              apply And.intro
              {
                apply iH
                intros X' t' p' sub
                cases sub with
                | aenc_key => exact And.left uH_ih
                | trans_aenc_key sub => 
                  apply And.right uH_ih
                  exact sub
                | aenc_term => exact And.left tH_ih
                | trans_aenc_term sub => 
                  apply And.right tH_ih
                  exact sub
              }
              {
                intros X' t' p' sub
                cases sub with
                | aenc_key => exact And.left uH_ih
                | trans_aenc_key sub => 
                  apply And.right uH_ih
                  exact sub
                | aenc_term => exact And.left tH_ih
                | trans_aenc_term sub => 
                  apply And.right tH_ih
                  exact sub
              }
          
          }
          intros X t p
          apply And.left (Q p)

noncomputable def TermMonotonicity (X Y: TermSet) : ∀   (t: Term), (dy X t) → (X ⊆ Y) →  (dy Y t) :=
  by
    intros t dyxt subset
    induction dyxt with
    | ax inH => exact dy.ax (subset inH)
    | pk _ kH_ih => exact dy.pk kH_ih  
    | splitL _ splitH_iH => exact dy.splitL splitH_iH
    | splitR _ splitH_iH => exact dy.splitR splitH_iH
    | pair _ _ tH_iH uH_iH => exact dy.pair tH_iH uH_iH
    | sdec _ _ encH_iH kH_iH => exact dy.sdec encH_iH kH_iH
    | senc _ _ tH_ih kH_iH => exact dy.senc tH_ih kH_iH
    | adec _ _ encH_iH kH_iH => exact dy.adec encH_iH kH_iH
    | aenc _ _ tH_ih kH_iH =>  exact dy.aenc tH_ih kH_iH


inductive NormalProof: ∀ {X: TermSet} {t: Term}, dy X t → Prop
| ax {X: TermSet} {t: Term} (inH:  t ∈ X) : NormalProof (dy.ax inH)
| pk {X: TermSet} {k: Name} {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) 
     : NormalProof (dy.pk kH)
| pair {X: TermSet} {t1 t2: Term} {tH: dy X t1} {uH: dy X t2} 
     (tN: NormalProof tH) (uN: NormalProof uH)
     : NormalProof (dy.pair tH uH)
| senc {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.priv k))} (tN: NormalProof tH) (kN: NormalProof kH): NormalProof (dy.senc tH kH)
| aenc {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.pub k))} (tN: NormalProof tH) (kN: NormalProof kH): NormalProof (dy.aenc tH kH)

| splitL_splitL {X: TermSet} {t₁ t₂ t₃: Term} {pH: dy X (Term.pair (Term.pair t₁ t₂) t₃)} (pN: NormalProof pH): NormalProof (dy.splitL (dy.splitL pH))
| splitL_splitR {X: TermSet} {t₁ t₂ t₃: Term} {pH: dy X (Term.pair t₃ (Term.pair t₁ t₂))} (pN: NormalProof pH): NormalProof (dy.splitL (dy.splitR pH))
| splitL_sdec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH: dy X (Term.key (Key.priv k))} {pH: dy X (Term.enc (Term.pair t₁ t₂) (Key.priv k))} (pN: NormalProof pH) (kN: NormalProof kH): NormalProof (dy.splitL (dy.sdec pH kH))
| splitL_adec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH: dy X (Term.key (Key.priv k))} {pH: dy X (Term.enc (Term.pair t₁ t₂) (Key.pub k))} (pN: NormalProof pH) (kN: NormalProof kH): NormalProof (dy.splitL (dy.adec pH kH))

| splitR_splitL {X: TermSet} {t₁ t₂ t₃: Term} {pH: dy X (Term.pair (Term.pair t₂ t₁) t₃)} (pN: NormalProof pH): NormalProof (dy.splitR (dy.splitL pH))
| splitR_splitR {X: TermSet} {t₁ t₂ t₃: Term} {pH: dy X (Term.pair t₃ (Term.pair t₂ t₁))} (pN: NormalProof pH): NormalProof (dy.splitR (dy.splitR pH))
| splitR_sdec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH: dy X (Term.key (Key.priv k))} {pH: dy X (Term.enc (Term.pair t₂ t₁) (Key.priv k))} (pN: NormalProof pH) (kN: NormalProof kH): NormalProof (dy.splitR (dy.sdec pH kH))
| splitR_adec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH: dy X (Term.key (Key.priv k))} {pH: dy X (Term.enc (Term.pair t₂ t₁) (Key.pub k))} (pN: NormalProof pH) (kN: NormalProof kH): NormalProof (dy.splitR (dy.adec pH kH))

| sdec_splitL {X: TermSet} {t₁ t₂: Term} {k: Name} {pH: dy X (Term.pair (Term.enc t₁ (Key.priv k)) t₂)} (pN: NormalProof pH) {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) : NormalProof (dy.sdec (dy.splitL pH) kH)
| sdec_splitR {X: TermSet} {t₁ t₂: Term} {k: Name} {pH: dy X (Term.pair t₂ (Term.enc t₁ (Key.priv k)))} (pN: NormalProof pH) {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) : NormalProof (dy.sdec (dy.splitR pH) kH)
| sdec_sdec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH: dy X (Term.enc (Term.enc t (Key.priv k₁)) (Key.priv k₂))} {k₁H: dy X (Term.key (Key.priv k₁))} {k₂H: dy X (Term.key (Key.priv k₂))} (pN: NormalProof pH) (k₁N: NormalProof k₁H) (k₂N: NormalProof k₂H) : NormalProof (dy.sdec (dy.sdec pH k₂H) k₁H)
| sdec_adec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH: dy X (Term.enc (Term.enc t (Key.priv k₁)) (Key.pub k₂))} {k₁H: dy X (Term.key (Key.priv k₁))} {k₂H: dy X (Term.key (Key.priv k₂))} (pN: NormalProof pH) (k₁N: NormalProof k₁H) (k₂N: NormalProof k₂H) : NormalProof (dy.sdec (dy.adec pH k₂H) k₁H)

| adec_splitL {X: TermSet} {t₁ t₂: Term} {k: Name} {pH: dy X (Term.pair (Term.enc t₁ (Key.pub k)) t₂)} (pN: NormalProof pH) {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) : NormalProof (dy.adec (dy.splitL pH) kH)
| adec_splitR {X: TermSet} {t₁ t₂: Term} {k: Name} {pH: dy X (Term.pair t₂ (Term.enc t₁ (Key.pub k)))} (pN: NormalProof pH) {kH: dy X (Term.key (Key.priv k))} (kN: NormalProof kH) : NormalProof (dy.adec (dy.splitR pH) kH)
| adec_sdec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH: dy X (Term.enc (Term.enc t (Key.pub k₁)) (Key.priv k₂))} {k₁H: dy X (Term.key (Key.priv k₁))} {k₂H: dy X (Term.key (Key.priv k₂))} (pN: NormalProof pH) (k₁N: NormalProof k₁H) (k₂N: NormalProof k₂H) : NormalProof (dy.adec (dy.sdec pH k₂H) k₁H)
| adec_adec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH: dy X (Term.enc (Term.enc t (Key.pub k₁)) (Key.pub k₂))} {k₁H: dy X (Term.key (Key.priv k₁))} {k₂H: dy X (Term.key (Key.priv k₂))} (pN: NormalProof pH) (k₁N: NormalProof k₁H) (k₂N: NormalProof k₂H) : NormalProof (dy.adec (dy.adec pH k₂H) k₁H)





def isNormalDy {X: TermSet} {t: Term} (proof: dy X t): Bool :=
    match proof with
    | dy.ax _ =>  true
    | dy.pk kH =>  (isNormalDy kH)
    | dy.splitL splitH =>            
                    match splitH with
                    | dy.pair _ _ =>  false
                    | _ => isNormalDy splitH
    | dy.splitR splitH =>            
                    match splitH with
                    | dy.pair _ _ =>  false
                    | _ => isNormalDy splitH
    | dy.pair tH uH =>  isNormalDy tH && isNormalDy uH
    | dy.senc tH kH =>  isNormalDy tH && isNormalDy kH
    | dy.aenc tH kH =>  isNormalDy tH && isNormalDy kH
    | dy.sdec encH kH => isNormalDy kH &&
                      match encH with
                      | dy.senc _ _ =>  false
                      | _ => isNormalDy encH
    | dy.adec encH kH => isNormalDy kH &&
                      match encH with
                      | dy.aenc _ _ =>  false
                      | _ => isNormalDy encH
@[simp]
def dyProofMeasure {X: TermSet} {t: Term} (proof: dy X t): Nat := 
      1 +
      match proof with
      | dy.ax _ =>  0
      | dy.pk kH =>  dyProofMeasure kH
      | dy.splitL splitH =>  dyProofMeasure splitH
      | dy.splitR splitH =>  dyProofMeasure splitH
      | dy.pair tH uH =>  dyProofMeasure tH + dyProofMeasure uH
      | dy.senc tH kH =>   dyProofMeasure tH + dyProofMeasure kH
      | dy.aenc tH kH =>   dyProofMeasure tH + dyProofMeasure kH
      | dy.sdec encH kH =>  dyProofMeasure encH + dyProofMeasure kH
      | dy.adec encH kH =>  dyProofMeasure encH + dyProofMeasure kH

@[simp]
def dyProofRewrite {X: TermSet} {t: Term} (proof: dy X t): dy X t :=
  match proof with
  | dy.splitL splitH =>
              match splitH with
              | dy.pair uH _ => uH
              | _ => proof
  | dy.splitR splitH =>
              match splitH with
              | dy.pair _ tH => tH
              | _ => proof
  | dy.sdec encH _ =>
              match encH with
              | dy.senc  tH _ => tH
              | _ => proof
  | dy.adec encH _ =>
              match encH with
              | dy.aenc  tH _ => tH
              | _ => proof
  | _ => proof

inductive RewriteBigStep: ∀ {X: TermSet} {t: Term}, dy X t -> dy X t -> Prop
| ax {X: TermSet} {t: Term} (inH:  t ∈ X) : RewriteBigStep (dy.ax inH) (dy.ax inH)
| pk {X: TermSet} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') 
     : RewriteBigStep (dy.pk kH) (dy.pk kH')
| pair {X: TermSet} {t₁ t₂: Term} {tH tH': dy X t₁} {uH uH': dy X t₂} 
     (tN: RewriteBigStep tH tH') (uN: RewriteBigStep uH uH')
     : RewriteBigStep (dy.pair tH uH) (dy.pair tH' uH')
| senc {X: TermSet} {t: Term} {k: Name} {tH tH': dy X t} {kH kH': dy X (Term.key (Key.priv k))} (tN: RewriteBigStep tH tH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.senc tH kH) (dy.senc tH' kH')
| aenc {X: TermSet} {t: Term} {k: Name} {tH tH': dy X t} {kH kH': dy X (Term.key (Key.pub k))} (tN: RewriteBigStep tH tH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.aenc tH kH) (dy.aenc tH' kH')

| splitL_splitL {X: TermSet} {t₁ t₂ t₃: Term} {pH pH' : dy X (Term.pair (Term.pair t₁ t₂) t₃)} (pN: RewriteBigStep pH pH'): RewriteBigStep (dy.splitL (dy.splitL pH)) (dy.splitL (dy.splitL pH'))
| splitL_splitR {X: TermSet} {t₁ t₂ t₃: Term} {pH pH': dy X (Term.pair t₃ (Term.pair t₁ t₂))} (pN: RewriteBigStep pH pH'): RewriteBigStep (dy.splitL (dy.splitR pH)) (dy.splitL (dy.splitR pH'))
| splitL_sdec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} {pH pH': dy X (Term.enc (Term.pair t₁ t₂) (Key.priv k))} (pN: RewriteBigStep pH pH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.splitL (dy.sdec pH kH)) (dy.splitL (dy.sdec pH' kH'))
| splitL_adec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} {pH pH': dy X (Term.enc (Term.pair t₁ t₂) (Key.pub k))} (pN: RewriteBigStep pH pH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.splitL (dy.adec pH kH)) (dy.splitL (dy.adec pH' kH'))
| splitL_pair {X: TermSet} {t₁ t₂: Term} {tH tH': dy X t₁} {uH uH': dy X t₂} 
     (tN: RewriteBigStep tH tH') (uN: RewriteBigStep uH uH')
  : RewriteBigStep (dy.splitL (dy.pair tH uH)) tH'



| splitR_splitL {X: TermSet} {t₁ t₂ t₃: Term} {pH pH': dy X (Term.pair (Term.pair t₂ t₁) t₃)} (pN: RewriteBigStep pH pH'): RewriteBigStep (dy.splitR (dy.splitL pH)) (dy.splitR (dy.splitL pH'))
| splitR_splitR {X: TermSet} {t₁ t₂ t₃: Term} {pH pH': dy X (Term.pair t₃ (Term.pair t₂ t₁))} (pN: RewriteBigStep pH pH'): RewriteBigStep (dy.splitR (dy.splitR pH)) (dy.splitR (dy.splitR pH'))
| splitR_sdec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} {pH pH': dy X (Term.enc (Term.pair t₂ t₁) (Key.priv k))} (pN: RewriteBigStep pH pH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.splitR (dy.sdec pH kH)) (dy.splitR (dy.sdec pH' kH'))
| splitR_adec {X: TermSet} {t₁ t₂: Term} {k: Name} {kH kH': dy X (Term.key (Key.priv k))} {pH pH': dy X (Term.enc (Term.pair t₂ t₁) (Key.pub k))} (pN: RewriteBigStep pH pH') (kN: RewriteBigStep kH kH'): RewriteBigStep (dy.splitR (dy.adec pH kH)) (dy.splitR (dy.adec pH' kH'))
| splitR_pair {X: TermSet} {t₁ t₂: Term} {tH tH': dy X t₁} {uH uH': dy X t₂} 
     (tN: RewriteBigStep tH tH') (uN: RewriteBigStep uH uH')
  : RewriteBigStep (dy.splitR (dy.pair tH uH)) uH'

| sdec_splitL {X: TermSet} {t₁ t₂: Term} {k: Name} {pH pH': dy X (Term.pair (Term.enc t₁ (Key.priv k)) t₂)} (pN: RewriteBigStep pH pH') {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') : RewriteBigStep (dy.sdec (dy.splitL pH ) kH ) (dy.sdec (dy.splitL pH') kH')
| sdec_splitR {X: TermSet} {t₁ t₂: Term} {k: Name} {pH pH': dy X (Term.pair t₂ (Term.enc t₁ (Key.priv k)))} (pN: RewriteBigStep pH pH') {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') : RewriteBigStep (dy.sdec (dy.splitR pH) kH) (dy.sdec (dy.splitR pH') kH')
| sdec_sdec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH pH': dy X (Term.enc (Term.enc t (Key.priv k₁)) (Key.priv k₂))} {k₁H k₁H': dy X (Term.key (Key.priv k₁))} {k₂H k₂H': dy X (Term.key (Key.priv k₂))} (pN: RewriteBigStep pH pH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H') : RewriteBigStep (dy.sdec (dy.sdec pH k₂H) k₁H) (dy.sdec (dy.sdec pH' k₂H') k₁H')
| sdec_adec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH pH': dy X (Term.enc (Term.enc t (Key.priv k₁)) (Key.pub k₂))} {k₁H k₁H': dy X (Term.key (Key.priv k₁))} {k₂H k₂H': dy X (Term.key (Key.priv k₂))} (pN: RewriteBigStep pH pH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H') : RewriteBigStep (dy.sdec (dy.adec pH  k₂H ) k₁H ) (dy.sdec (dy.adec pH' k₂H' ) k₁H')
| sdec_senc {X: TermSet} {t: Term} {k: Name} {tH tH': dy X t} {k₁H k₁H': dy X (Term.key (Key.priv k))} {k₂H k₂H': dy X (Term.key (Key.priv k))} (tN: RewriteBigStep tH tH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H'): RewriteBigStep (dy.sdec (dy.senc tH k₁H) k₂H) tH'

| adec_splitL {X: TermSet} {t₁ t₂: Term} {k: Name} {pH pH': dy X (Term.pair (Term.enc t₁ (Key.pub k)) t₂)} (pN: RewriteBigStep pH pH') {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') : RewriteBigStep (dy.adec (dy.splitL pH ) kH ) (dy.adec (dy.splitL pH' ) kH' )
| adec_splitR {X: TermSet} {t₁ t₂: Term} {k: Name} {pH pH': dy X (Term.pair t₂ (Term.enc t₁ (Key.pub k)))} (pN: RewriteBigStep pH pH') {kH kH': dy X (Term.key (Key.priv k))} (kN: RewriteBigStep kH kH') : RewriteBigStep (dy.adec (dy.splitR pH ) kH ) (dy.adec (dy.splitR pH' ) kH' )
| adec_sdec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH pH': dy X (Term.enc (Term.enc t (Key.pub k₁)) (Key.priv k₂))} {k₁H k₁H': dy X (Term.key (Key.priv k₁))} {k₂H k₂H': dy X (Term.key (Key.priv k₂))} (pN: RewriteBigStep pH pH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H') : RewriteBigStep (dy.adec (dy.sdec pH  k₂H ) k₁H ) (dy.adec (dy.sdec pH'  k₂H' ) k₁H' )
| adec_adec {X: TermSet} {t: Term} {k₁ k₂: Name} {pH pH': dy X (Term.enc (Term.enc t (Key.pub k₁)) (Key.pub k₂))} {k₁H k₁H': dy X (Term.key (Key.priv k₁))} {k₂H k₂H': dy X (Term.key (Key.priv k₂))} (pN: RewriteBigStep pH pH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H') : RewriteBigStep (dy.adec (dy.adec pH  k₂H ) k₁H ) (dy.adec (dy.adec pH'  k₂H' ) k₁H' )
| adec_aenc {X: TermSet} {t: Term} {k: Name} {tH tH': dy X t} {k₁H k₁H': dy X (Term.key (Key.pub k))} {k₂H k₂H': dy X (Term.key (Key.priv k))} (tN: RewriteBigStep tH tH') (k₁N: RewriteBigStep k₁H k₁H') (k₂N: RewriteBigStep k₂H k₂H'): RewriteBigStep (dy.adec (dy.aenc tH k₁H) k₂H) tH'



@[simp]
lemma dyProofRewriteSmaller: ∀ {X: TermSet} {t: Term} (proof: dy X t), 
  dyProofMeasure (dyProofRewrite proof) ≤ dyProofMeasure proof :=
  by
    intros X t proof
    cases proof with
    | splitL splitH  => 
             simp
             cases splitH with
             | pair tH uH => 
                    simp
                    omega
             | _ => simp
    
    | splitR splitH  => 
             simp
             cases splitH with
             | pair tH uH => 
                    simp
                    omega
             | _ => simp
    | sdec encH  _ => 
                simp
                cases encH with
                | senc _ _ => simp
                              omega
                | _ => simp
    | adec encH  _ => 
                simp
                cases encH with
                | aenc _ _ => simp
                              omega
                | _ => simp
    | _ => simp

@[simp]
def recursiveDyProofRewriter {X: TermSet} {t: Term} (p: dy X t) : dy X t :=
    match p with
    | dy.ax inH => dyProofRewrite (dy.ax inH)
    | dy.pk kH => dyProofRewrite (  dy.pk (recursiveDyProofRewriter kH))
    | dy.splitL splitH => dyProofRewrite ( dy.splitL (recursiveDyProofRewriter splitH))
    | dy.splitR splitH => dyProofRewrite ( dy.splitR (recursiveDyProofRewriter splitH))
    | dy.pair tH uH => dyProofRewrite (  dy.pair (recursiveDyProofRewriter tH) (recursiveDyProofRewriter uH))
    | dy.senc tH kH => dyProofRewrite (  dy.senc (recursiveDyProofRewriter tH) (recursiveDyProofRewriter kH)) 
    | dy.aenc tH kH => dyProofRewrite (  dy.aenc (recursiveDyProofRewriter tH) (recursiveDyProofRewriter kH))
    | dy.sdec encH kH => dyProofRewrite ( dy.sdec (recursiveDyProofRewriter encH) (recursiveDyProofRewriter kH))
    | dy.adec encH kH => dyProofRewrite ( dy.adec (recursiveDyProofRewriter encH) (recursiveDyProofRewriter kH))

@[simp]
def repeat_apply {A: Type} : Nat → (A → A) → A → A
| 0 => fun _ a => a 
| n + 1 => fun f a => f (repeat_apply n f a)

lemma repeatRight: ∀ {A: Type} (n: Nat) (f: A -> A) (a: A), repeat_apply (n + 1) f a = repeat_apply n f (f a) :=
  by
    intros A n f
    induction n with
    | zero => 
           intros a
           simp
    | succ n iHn =>
           intros a
           simp
           simp at iHn
           rw [iHn]
         
theorem rewriterNormaliserFun: ∀ {X: TermSet} {t: Term} (p: dy X t), isNormalDy (recursiveDyProofRewriter p) = true :=
   by
    intros X t p
    induction p with
    | ax => simp [isNormalDy]
    | pk => simp ; assumption
    | splitL splitH splitH_iH =>
      simp
      cases E: recursiveDyProofRewriter splitH
      any_goals  (simp ; unfold isNormalDy ; simp <;> rw [← E] <;> assumption)
      case splitL.pair tH uH =>
        simp
        rw [E] at splitH_iH
        unfold isNormalDy at splitH_iH
        simp at splitH_iH
        apply And.left splitH_iH
    | splitR splitH splitH_iH =>
      simp
      cases E: recursiveDyProofRewriter splitH
      any_goals  (simp ; unfold isNormalDy ; simp <;> rw [← E] <;> assumption)
      case splitR.pair tH uH =>
        simp
        rw [E] at splitH_iH
        unfold isNormalDy at splitH_iH
        simp at splitH_iH
        apply And.right splitH_iH
    | pair tH uH tH_iH uH_iH =>
      unfold isNormalDy
      simp
      apply And.intro tH_iH uH_iH
    | sdec encH kH encH_iH kH_iH =>
      simp
      cases E: recursiveDyProofRewriter encH   
      any_goals (simp ; unfold isNormalDy ; simp <;> rw [← E] <;> apply And.intro <;> assumption)
      case sdec.senc kH =>
        simp
        rw [E] at encH_iH
        unfold isNormalDy at encH_iH
        simp at encH_iH
        apply And.left encH_iH

    | adec encH kH encH_iH kH_iH =>
      simp
      cases E: recursiveDyProofRewriter encH   
      any_goals (simp ; unfold isNormalDy ; simp <;> rw [← E] <;> apply And.intro <;> assumption)
      case adec.aenc kH =>
        simp
        rw [E] at encH_iH
        unfold isNormalDy at encH_iH
        simp at encH_iH
        apply And.left encH_iH
    | aenc _ _ ih1 ih2 =>
      unfold isNormalDy
      simp
      apply And.intro ih1 ih2
    | senc _ _ ih1 ih2 =>
      unfold isNormalDy
      simp
      apply And.intro ih1 ih2

theorem rewriterNormaliser: ∀ {X: TermSet} {t: Term} (p p': dy X t), RewriteBigStep p p' → NormalProof p' :=
  by
    intros X t p p' RW
    induction RW 
    any_goals (constructor <;> assumption)
    all_goals (assumption)


inductive SubTerm: Term -> Term -> Prop
| refl (t: Term) : SubTerm t t
                                                                     
| pair_left (t₁ t₂: Term) : SubTerm t₁ (Term.pair t₁ t₂)
| pair_right (t₁ t₂: Term) : SubTerm t₂ (Term.pair t₁ t₂)
                                            
| enc_term (t : Term) (k: Key) : SubTerm t (Term.enc t k)
| enc_key (t: Term) (k: Key) : SubTerm (Term.key k) (Term.enc t k)
| trans {t₁ t₂ t₃} (p₁: SubTerm t₁ t₂) (p₂: SubTerm t₂ t₃): SubTerm t₁ t₃     
    
@[simp]
def SubTermSet (S: TermSet) : Set Term := {x | ∃ t, t ∈ S ∧ SubTerm x t}

@[simp]
def ProofTerms {X: TermSet} {t: Term} (p: dy X t) : TermSet :=
  match p with
  | @dy.ax _ t _ => {t}
  | @dy.pk _ k kH => {Term.key (Key.pub k)} ∪ (ProofTerms kH)
  | @dy.splitL _ t1 _ splitH =>  {t1} ∪ (ProofTerms splitH)
  | @dy.splitR _ _ t2 splitH =>  {t2} ∪ (ProofTerms splitH)
  | @dy.pair _ t1 t2 t1H t2H => {Term.pair t1 t2} ∪ (ProofTerms t1H) ∪ (ProofTerms t2H)
  | @dy.sdec _ t' _ encH kH => {t'} ∪  (ProofTerms encH) ∪ (ProofTerms kH)
  | @dy.senc _ t' k tH kH =>   {Term.enc t' (Key.priv k)} ∪  (ProofTerms tH) ∪ (ProofTerms kH)
  | @dy.adec _ t' _ encH kH => {t'} ∪  (ProofTerms encH) ∪ (ProofTerms kH)
  | @dy.aenc _ t' k tH kH =>   {Term.enc t' (Key.pub k)} ∪  (ProofTerms tH) ∪ (ProofTerms kH)

theorem SubTermProperty: forall (X: TermSet) (t: Term) (p: dy X t), ((isNormalDy p) = true)
                                                                       -> match p  with
                                                                          | dy.pair _ _ => ProofTerms p ⊆ SubTermSet (X ∪ {t})
                                                                          | dy.senc _ _ => ProofTerms p ⊆ SubTermSet (X ∪ {t})
                                                                          | dy.aenc _ _ => ProofTerms p ⊆ SubTermSet (X ∪ {t})
                                                                          | dy.pk _ => ProofTerms p ⊆ SubTermSet (X ∪ {t})
                                                                          | _ => ProofTerms p ⊆ SubTermSet X
                                                                          :=
        by
          intros X _ p
          induction p with
          | @ax t inH => 
            intros H
            simp
            exists t
            apply And.intro inH
            constructor
          | @splitL t1 t2 splitH splitH_ih =>
            simp
            intros H
            cases splitH with
            | pair =>
              simp [isNormalDy] at H
            | splitL splitH =>
              unfold isNormalDy at H
              simp at H
              specialize (splitH_ih H)
              simp at splitH_ih
              simp [insert, Set.insert]
              simp [insert, Set.insert] at splitH_ih 
              cases splitH_ih with
              | intro left right =>
              apply And.intro
              {
                cases left with
                | intro w wH =>
                exists w
                cases wH with
                | intro left right =>
                apply And.intro left
                apply SubTerm.trans (p₂:= right)
                constructor     
              }
              {
                apply And.intro left right
              }
            | splitR splitH =>
              unfold isNormalDy at H
              simp at H
              specialize (splitH_ih H)
              simp at splitH_ih
              simp [insert, Set.insert]
              simp [insert, Set.insert] at splitH_ih 
              cases splitH_ih with
              | intro left right =>
              apply And.intro
              {
                cases left with
                | intro w wH =>
                exists w
                cases wH with
                | intro left right =>
                apply And.intro left
                apply SubTerm.trans (p₂:= right)
                constructor     
              }
              {
                apply And.intro left right
              }
            | sdec kH encH =>
              unfold isNormalDy at H
              simp at H
              specialize (splitH_ih H)
              simp at splitH_ih
              simp [insert, Set.insert]
              simp [insert, Set.insert] at splitH_ih
              
              cases splitH_ih with
              | intro left right =>
              cases left with
              | intro leftleft leftright =>
              apply And.intro
              {
                cases leftleft with
                | intro w wH =>
                exists w
                cases wH with
                | intro left right =>
                apply And.intro left
                apply SubTerm.trans (p₂:= right)
                constructor     
              }
              {
                intro a
                intro H
                
                sorry
              }
                
              
                
                
            | _ => sorry
            
            
            
            
            
          | _ => sorry
          


inductive Assertion: Type
| eq (t u: Term)
| member (t₀: Term) (tlist: List Term)
| and (a₀ a₁ : Assertion)
| exist (a: Assertion) (x: Var)
| says (k: Name) (a: Assertion)
deriving DecidableEq



def FVSetAssertion (a: Assertion): Set Var :=
  match a with
  | Assertion.eq l r => FVSetTerm l ∪ FVSetTerm r
  | Assertion.member t tlist => FVSetTerm t ∪ List.foldr (fun t s => FVSetTerm t ∪ s) ∅ tlist
  | Assertion.and a₀ a₁ => FVSetAssertion a₀ ∪ FVSetAssertion a₁
  | Assertion.exist a x => FVSetAssertion a \ {x}
  | Assertion.says _ a => FVSetAssertion a

def FVSetTermSet (S: TermSet) : Set Var :=
  {x | ∃ t, t ∈ S ∧ x ∈ FVSetTerm t}

abbrev AssertionSet := Set Assertion

def FVSetAssertionSet (A: AssertionSet): Set Var :=
  {x | ∃ a, a ∈ A ∧ x ∈ FVSetAssertion a}


inductive TermSubTermPosition: Term → Term → List ℕ → Prop
| epsilon (t: Term): TermSubTermPosition t t []
| pair_left₀ {t t₁ t₂: Term} {pos: List ℕ} (proof: TermSubTermPosition t (Term.pair t₁ t₂) pos) : TermSubTermPosition t t₁ (0::pos)
| pair_right₁ {t t₁ t₂: Term} {pos: List ℕ} (proof: TermSubTermPosition t (Term.pair t₁ t₂) pos) : TermSubTermPosition t t₁ (0::pos)
| enc_term₀ (t t': Term) (k: Key) {pos: List ℕ} (proof: TermSubTermPosition t (Term.enc t' k) pos) : TermSubTermPosition t t' (0::pos)
| enc_name₁ (t t': Term) (k: Key) {pos: List ℕ} (proof: TermSubTermPosition t (Term.enc t' k) pos) : TermSubTermPosition t (Term.key k) (1::pos)

def TermPositionSet (t: Term) : Set (List ℕ):=
  {pos | ∃ t', TermSubTermPosition t t' pos}

inductive AssertionTermPosition: Assertion -> Term -> List ℕ -> Prop
| eq_left0 {t tsub: Term} {pos: List ℕ} (proof: TermSubTermPosition t tsub pos) (t': Term) : AssertionTermPosition (Assertion.eq t t') tsub (0::pos)
| eq_right₁ {t t' t'sub: Term} {pos: List ℕ} (t: Term)(proof: TermSubTermPosition t t'sub pos) : AssertionTermPosition (Assertion.eq t t') t'sub (1::pos)
| member_member₀  (t: Term) (tlist: List Term) : AssertionTermPosition (Assertion.member t tlist) t [0]
| member_disjunctionSi {i: Nat} {t: Term} {tlist: List Term} (t': Term) (proof: tlist[i]? = Option.some t): AssertionTermPosition (Assertion.member t' tlist) t' [(Nat.succ i)]
                                                                                                                                                        
| and_left₀ {a : Assertion} {tsub: Term} {pos: List Nat} (a' : Assertion) (proof: AssertionTermPosition a tsub pos) : AssertionTermPosition (Assertion.and a a') tsub (0::pos)
| and_right₁ {a': Assertion} {tsub: Term} {pos: List ℕ} (a: Assertion) (proof: AssertionTermPosition a' tsub pos) : AssertionTermPosition (Assertion.and a a') tsub (1::pos)

| exist_var₀ {a: Assertion} {pos: List Nat} {tsub: Term} {x: Var}  (proof: AssertionTermPosition a (var_to_term x) pos) : AssertionTermPosition (Assertion.exist a x) (var_to_term x) (0::pos)

| says_name₀₀ (k: Name) (a: Assertion): AssertionTermPosition (Assertion.says k a) (Term.name k) [0,0]
| says_key₀ (k: Name) (a: Assertion): AssertionTermPosition (Assertion.says k a) (Term.key (Key.pub k)) [0]
| says_ass₁ {a: Assertion} (k: Name) {tsub: Term} {pos: List ℕ} (proof: AssertionTermPosition a tsub pos): AssertionTermPosition (Assertion.says k a) tsub (1::pos)

def AssertionPositionSet (a: Assertion) : Set (List ℕ):=
  {pos | ∃ t', AssertionTermPosition a t' pos}

def AssertionTermPositionSet (a: Assertion) (t: Term) : Set (List ℕ) :=
  {pos | AssertionTermPosition a t pos}

inductive ProperPrefix: List ℕ -> List ℕ -> Prop
| hd (hd: Nat) {tl: List Nat} (nonempty: tl ≠ []) : ProperPrefix [hd] (hd::tl)
| cons {hd: Nat} {tl1 tl2: List Nat} (proof: ProperPrefix tl1 tl2) : ProperPrefix (hd::tl1) (hd::tl2)

def AssertionSubTerm (a: Assertion) (t: Term) := ∃ pos, AssertionTermPosition a t pos

def AssertionSubTermSet (a: Assertion) : TermSet := {t | AssertionSubTerm a t}
def AssertionSetSubTermSet (A: AssertionSet) : TermSet:= {t | ∃ a, a ∈ A ∧ AssertionSubTerm a t}



def AssertionMaximalSubTerm (a: Assertion) (t: Term) :=
 ∃ pos, (AssertionTermPosition a t pos ∧ (¬ (∃ t' pos', AssertionTermPosition a t' pos' ∧ ProperPrefix pos' pos)))

def QSet (pos: List ℕ) : Set (List ℕ) :=
{ pos' | pos' = [] ∨ ProperPrefix pos' pos }

inductive AbstractablePositionSetTerm : TermSet → Term → Set (List ℕ)
| cons {S: TermSet} {t: Term} {p: List ℕ} (positionTermProof: p ∈(TermPositionSet t))(abstractableProof: forall (q: List Nat) (t': Term), q ∈ (QSet p) -> TermSubTermPosition t t' q -> dy S t') : AbstractablePositionSetTerm S t p

inductive AbstractablePositionSetAssertion: TermSet -> Assertion -> Set (List ℕ)
| eq_left₀ {S: TermSet} {t₀: Term} {pos: List ℕ} (t₁: Term) (proof: AbstractablePositionSetTerm S t₀ pos) : AbstractablePositionSetAssertion S (Assertion.eq t₀ t₁) (0::pos)
| eq_right₁ {S: TermSet} {t₁: Term} {pos: List ℕ} (t₀: Term) (proof: AbstractablePositionSetTerm S t₁ pos): AbstractablePositionSetAssertion S (Assertion.eq t₀ t₀) (1::pos)
| member₀ (S: TermSet) {n: ℕ} (t₀: Term) (tList : List Term) : AbstractablePositionSetAssertion S (Assertion.member t₀ tList) [0]
| and_left₀ {S:TermSet} {a : Assertion} {pos: List ℕ} (proof: pos ∈ (AbstractablePositionSetAssertion S a)) (a' : Assertion): AbstractablePositionSetAssertion S (Assertion.and a a') (0::pos)
| and_right₁ {S: TermSet} {a': Assertion} {pos: List ℕ} (a: Assertion) (proof: pos ∈ AbstractablePositionSetAssertion S a'): AbstractablePositionSetAssertion S (Assertion.and a a') (1::pos)
| exists_var₀ {S: TermSet} {pos: List ℕ} (a: Assertion) {x: Var} (proof: pos ∈ AbstractablePositionSetAssertion ( S ∪ {var_to_term x}) a):
  AbstractablePositionSetAssertion S (Assertion.exist a x)
    (0::pos)
| says_pub₀ (S: TermSet) (k: Name) (a: Assertion) : AbstractablePositionSetAssertion S (Assertion.says k a) [0]
| says_ass₁ {S: TermSet} (k: Name) {a: Assertion} {pos: List ℕ} (proof: pos ∈ AbstractablePositionSetAssertion S a): AbstractablePositionSetAssertion S (Assertion.says k a) (1::pos)



inductive SubstitutedAssertion: Assertion -> Set (List ℕ) -> Term -> Assertion -> Type
-- | cons
--     {a a': Assertion} {t: Term} {P: Set (List ℕ)}
--     (includedProof:  P ⊆ (AssertionPositionSet a))
--     (termPositionSubstitutedProof: ∀ pos,
--          pos ∈ P -> AssertionTermPosition a' t pos
--     )
--     (termPositionSameProof: forall pos t',
--         ¬(pos ∈ P) -> AssertionTermPosition a t pos -> AssertionTermPosition a' t' pos
--     )
--   : SubstitutedAssertion a P t a'.


@[simp]
def intersection {A: Type} [DecidableEq A]: List A -> List A -> List A
| [], _ => []
| hd::tl, l => if (hd ∈ l ∧ hd ∉ (intersection tl l)) 
                 then hd::(intersection tl l)
                 else intersection tl l


lemma intersection_assoc {A: Type} [inst: DecidableEq A]: ∀ (l1 l2 l3: List A), intersection l1 (intersection l2 l3) = intersection (intersection l1 l2) l3 :=
  by
    intros l1 l2 l3
    induction l1 with
    | nil => simp
    | cons hd tl tl_ih =>
      simp
      
      sorry
      
    
mutual                   
inductive eq_ady: TermSet -> AssertionSet -> Assertion -> Type
| ax (S: TermSet) {A: AssertionSet} {alpha: Assertion} (proof: alpha ∈ A): eq_ady S A alpha
| eq {S: TermSet} (A: AssertionSet) {t: Term} (proof: dy S t) : eq_ady S A (Assertion.eq t t)
                                                                     
| cons_pair {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p1: eq_ady S A (Assertion.eq t1 u1)) (p2: eq_ady S A (Assertion.eq t2 u2)): eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))

| cons_enc {S: TermSet} {A: AssertionSet} {t1 t2: Term} {k1 k2: Key} (p1: eq_ady S A (Assertion.eq t1 t2)) (p2: eq_ady S A (Assertion.eq ((Term.key k1)) (Term.key k2 ))): eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))

| cons_pk {S: TermSet} {A: AssertionSet} {k1 k2: Name} (p: eq_ady S A (Assertion.eq ((Term.key (Key.priv k1))) (Term.key (Key.priv k2) )) ): eq_ady S A (Assertion.eq ((Term.key (Key.pub k1))) (Term.key (Key.pub k2) ))

| sym {S: TermSet} {A: AssertionSet} {t u: Term} (p: eq_ady S A (Assertion.eq t u)) : eq_ady S A (Assertion.eq u t)
 
| trans {S: TermSet} {A: AssertionSet} {t1 tk: Term} (p: Eq_Trans S A t1 tk): eq_ady S A (Assertion.eq t1 tk)

| proj_pair_left {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) (pin: {[0,0], [0, 1], [1, 0], [1, 1]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) ) : eq_ady S A (Assertion.eq t1 u1)
| proj_pair_right {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2)))  (pin: {[0,0], [0, 1], [1, 0], [1, 1]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))) ) : eq_ady S A (Assertion.eq t2 u2)
                                   
          
| proj_enc_term {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) (pin: {[0,0], [0, 1], [1, 0], [1, 1]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) ): eq_ady S A (Assertion.eq t1 t2)
| proj_enc_key {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) (pin: {[0,0], [0, 1], [1, 0], [1, 1]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) ): eq_ady S A (Assertion.eq (Term.key k1) (Term.key k2))

| proj_pk {S: TermSet} {A: AssertionSet} {k1 k2: Name} (p: eq_ady S A (Assertion.eq ((Term.key (Key.pub k1))) (Term.key (Key.pub k2)))) (pin: {[0,0], [1,0]} ⊆ (AbstractablePositionSetAssertion S (Assertion.eq ((Term.key (Key.pub k1))) (Term.key (Key.pub k2))) )): eq_ady S A (Assertion.eq ((Term.key (Key.priv k1))) (Term.key (Key.priv k2) ))

| subst {S: TermSet} {A: AssertionSet} {t u: Term} {l: List Term} (proofMember: eq_ady S A (Assertion.member t l)) (proofEq: eq_ady S A (Assertion.eq t u)): eq_ady S A (Assertion.member u l)

| prom {S: TermSet} {A: AssertionSet} {t n: Term} (proof: eq_ady S A (Assertion.member t [n])) : eq_ady S A (Assertion.eq t n)

| int {S: TermSet} {A: AssertionSet} {t: Term} {l: List Term} (premises: Eq_Int S A t l): eq_ady S A (Assertion.member t l)
| wk {S: TermSet} {A: AssertionSet} {t n: Term} {nlist: List Term} (proofEq: eq_ady S A (Assertion.eq t n)) (proofIn: n ∈ nlist) (proofValid: Eq_Wk S nlist): eq_ady S A (Assertion.member t nlist)

inductive Eq_Trans: TermSet -> AssertionSet -> Term -> Term -> Type
| two_trans {S: TermSet} {A: AssertionSet} {t1 t2 t3: Term} (p1: eq_ady S A (Assertion.eq t1 t2)) (p2: eq_ady S A (Assertion.eq t2 t3)): Eq_Trans S A t1 t3
| trans_trans {S: TermSet} {A: AssertionSet} {t1 tk tk': Term} (phead: eq_ady S A (Assertion.eq t1 tk)) (plist: Eq_Trans S A tk tk'): Eq_Trans S A t1 tk'                                                           
inductive Eq_Int: TermSet -> AssertionSet -> Term -> List Term -> Type
| two_lists {S: TermSet} {A: AssertionSet} {t: Term} {l1 l2: List Term}  (proof1: eq_ady S A (Assertion.member t l1)) (proof2: eq_ady S A (Assertion.member t l2)): Eq_Int S A t (intersection l1 l2)
| new_list {S: TermSet} {A: AssertionSet} {t: Term} {l l': List Term} (proof1: eq_ady S A (Assertion.member t l)) (proof2: Eq_Int S A t l'): Eq_Int S A t (intersection l l')
                                                                                                                                                                                                                                                                             
inductive Eq_Wk: TermSet -> List Term -> Type
| single {S: TermSet} {t: Term} (proof: dy S t): Eq_Wk S [t]
| new {S: TermSet} {t: Term} {tlist: List Term} (proofNew: dy S t) (proofList: Eq_Wk S tlist): Eq_Wk S (t::tlist)
end

@[simp]
def isCons {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a) : Bool :=
  match p with
  | eq_ady.cons_pair _ _ => Bool.true
  | eq_ady.cons_enc _ _ => Bool.true
  | eq_ady.cons_pk _ => Bool.true
  | _ => Bool.false
@[simp]
def isProj {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a) : Bool :=
  match p with
  | eq_ady.proj_pair_left .. => Bool.true
  | eq_ady.proj_pair_right .. => Bool.true
  | eq_ady.proj_enc_key .. => Bool.true
  | eq_ady.proj_enc_term .. => Bool.true
  | eq_ady.proj_pk .. => Bool.true
  | _ => Bool.false

mutual
def containsCons {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): Bool :=
  match proof with
  | eq_ady.ax .. => false
  | eq_ady.eq .. => false
  | eq_ady.cons_pair .. => true
  | eq_ady.cons_enc .. => true
  | eq_ady.cons_pk .. => true
  | eq_ady.sym p => containsCons p
  | eq_ady.trans plist => containsConsTrans plist
  | eq_ady.proj_pair_left p pin => containsCons p
  | eq_ady.proj_pair_right p pin => containsCons p
  | eq_ady.proj_enc_key p pin => containsCons p
  | eq_ady.proj_enc_term p pin => containsCons p
  | eq_ady.proj_pk p pin => containsCons p
  | eq_ady.subst p p' => containsCons p || containsCons p'
  | eq_ady.prom p => containsCons p
  | eq_ady.int premises => containsConsInt premises
  | eq_ady.wk p _ _ => containsCons p
def containsConsTrans  {S: TermSet} {A: AssertionSet} {t1 tk: Term} (plist: Eq_Trans S A t1 tk) : Bool :=
 match plist with
 | Eq_Trans.two_trans eq1 eq2 => containsCons eq1 || containsCons eq2
 | Eq_Trans.trans_trans phead plist => containsCons phead || containsConsTrans plist
def containsConsInt {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (premises: Eq_Int S A t tlist) : Bool :=
  match premises with
  | Eq_Int.two_lists x1 x2 => containsCons x1 || containsCons x2
  | Eq_Int.new_list xhead xlist => containsCons xhead || containsConsInt xlist
end

def containsReflexiveTrans {S: TermSet} {A: AssertionSet} {a1 a2: Term} (l: Eq_Trans S A a1 a2): Bool :=
    match l with
    | @Eq_Trans.two_trans _ _ t1 t2 t3 .. => 
      if Decidable.decide (t1 = t2) || Decidable.decide (t2 = t3) then true else false
    | @Eq_Trans.trans_trans _ _ t1 t2 _ _ plist => if Decidable.decide (t1 = t2) || containsReflexiveTrans plist then true else false

def  adjacentSafe {S: TermSet} {A: AssertionSet} {a1 a2: Term} (l: Eq_Trans S A a1 a2): Bool :=
  match l with
  | Eq_Trans.two_trans p1 p2 => !(isCons p1  && isCons p2)
  | Eq_Trans.trans_trans phead ptail => 
    adjacentSafe ptail &&
    (!((isCons phead) &&  
      match ptail with 
      | Eq_Trans.two_trans p2 _ => (isCons p2) 
      | Eq_Trans.trans_trans p2 _ => (isCons p2)))

mutual
  def isNormalEqAdy {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): Bool :=
    match proof with
    | eq_ady.ax .. => true
    | eq_ady.eq _ p => isNormalDy p &&
                       match p with
                       | dy.pair _ _ => false
                       | dy.senc _ _ => false
                       | dy.aenc _ _ => false
                       | dy.pk _ => false
                       | _ => true
    | eq_ady.cons_pair p1 p2 => isNormalEqAdy p1 && isNormalEqAdy p2
    | eq_ady.cons_enc p1 p2 => isNormalEqAdy p1 && isNormalEqAdy p2
    | eq_ady.cons_pk p => isNormalEqAdy p
    | eq_ady.sym p => isNormalEqAdy p &&
                      match p with
                      | eq_ady.ax .. => true
                      | eq_ady.prom .. => true
                      | _ => false
    | eq_ady.trans plist => isNormalEqTrans plist && adjacentSafe plist && !(containsReflexiveTrans plist)
    | eq_ady.proj_pair_left p _ => !(containsCons p) && isNormalEqAdy p
    | eq_ady.proj_pair_right p _ => !(containsCons p) && isNormalEqAdy p
    | eq_ady.proj_enc_key p _ => !(containsCons p) && isNormalEqAdy p
    | eq_ady.proj_enc_term p _ => !(containsCons p) && isNormalEqAdy p
    | eq_ady.proj_pk p _ => !(containsCons p) && isNormalEqAdy p
    | eq_ady.subst p p' => isNormalEqAdy p && isNormalEqAdy p'
    | eq_ady.prom p => isNormalEqAdy p
    | eq_ady.int premises => isNormalEqInt premises 
    | eq_ady.wk eqa _ dylist => isNormalEqAdy eqa && isNormalEqWk dylist
  def isNormalEqTrans  {S: TermSet} {A: AssertionSet} {t1 tk: Term} (plist: Eq_Trans S A t1 tk) : Bool :=
    match plist with
    | Eq_Trans.two_trans p1 p2 => isNormalEqAdy p1 && isNormalEqAdy p2
    | Eq_Trans.trans_trans phead plist => isNormalEqAdy phead && isNormalEqTrans plist
  def isNormalEqInt {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (premises: Eq_Int S A t tlist) : Bool :=
  let temp {S A a} (p: eq_ady S A a) :=
    match p with | eq_ady.int .. => false | eq_ady.wk .. => false | _ => true
    ;
    match premises with
    | Eq_Int.two_lists x1 x2 => isNormalEqAdy x1 && isNormalEqAdy x2 && temp x1 && temp x2
    | Eq_Int.new_list xhead xlist => isNormalEqAdy xhead && temp xhead && isNormalEqInt xlist
  def isNormalEqWk {S: TermSet} {ts: List Term} (l: Eq_Wk S ts): Bool :=
    match l with
    | Eq_Wk.single p => isNormalDy p
    | Eq_Wk.new phead plist => isNormalDy phead && isNormalEqWk plist
end

mutual
@[simp] 
def δ₁ {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): ℕ := 
    match proof with
    | eq_ady.ax .. => 0
    | eq_ady.eq _ p => dyProofMeasure p
    | eq_ady.cons_pair p1 p2 => δ₁ p1 + δ₁ p2
    | eq_ady.cons_enc p1 p2 => δ₁ p1 + δ₁ p2
    | eq_ady.cons_pk p => δ₁ p
    | eq_ady.sym p => δ₁ p
    | eq_ady.trans plist => δ₁Trans plist
    | eq_ady.proj_pair_left p _ => δ₁ p
    | eq_ady.proj_pair_right p _ => δ₁ p
    | eq_ady.proj_enc_key p _ => δ₁ p
    | eq_ady.proj_enc_term p _ => δ₁ p
    | eq_ady.proj_pk p _=> δ₁ p
    | eq_ady.subst p p' => δ₁ p + δ₁ p'
    | eq_ady.prom p => δ₁ p
    | eq_ady.int premises => δ₁Int premises
    | eq_ady.wk eqa _ dylist => δ₁ eqa + δ₁Wk dylist
@[simp]
  def δ₁Trans  {S: TermSet} {A: AssertionSet} {t1 tk: Term} (plist: Eq_Trans S A t1 tk) : ℕ :=
    match plist with
    | Eq_Trans.two_trans p1 p2 => δ₁ p1 + δ₁ p2 
    | Eq_Trans.trans_trans phead plist => δ₁ phead + δ₁Trans plist
@[simp]
  def δ₁Int {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (premises: Eq_Int S A t tlist) : ℕ :=
    match premises with
    | Eq_Int.two_lists x1 x2 => δ₁ x1 + δ₁ x2 
    | Eq_Int.new_list xhead xlist => δ₁ xhead + δ₁Int xlist
@[simp]
  def δ₁Wk {S: TermSet} {ts: List Term} (l: Eq_Wk S ts): ℕ :=
    match l with
    | Eq_Wk.single p => dyProofMeasure p
    | Eq_Wk.new phead plist => dyProofMeasure phead + δ₁Wk plist
end


mutual
@[simp] 
def δ₂ {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): ℕ := 
    match proof with
    | eq_ady.ax .. => 0
    | eq_ady.eq _ p => 0
    | eq_ady.cons_pair p1 p2 => 1 + δ₂ p1 + δ₂ p2
    | eq_ady.cons_enc p1 p2 => 1 + δ₂ p1 + δ₂ p2
    | eq_ady.cons_pk p => 1 + δ₂ p
    | eq_ady.sym p => δ₂ p
    | eq_ady.trans plist => δ₂Trans plist
    | eq_ady.proj_pair_left p _ => δ₂ p
    | eq_ady.proj_pair_right p _ => δ₂ p
    | eq_ady.proj_enc_key p _ => δ₂ p
    | eq_ady.proj_enc_term p _ => δ₂ p
    | eq_ady.proj_pk p _ => δ₂ p
    | eq_ady.subst p p' => δ₂ p + δ₂ p'
    | eq_ady.prom p => δ₂ p
    | eq_ady.int premises => δ₂Int premises
    | eq_ady.wk eqa _ dylist => δ₂ eqa
@[simp]
  def δ₂Trans  {S: TermSet} {A: AssertionSet} {t1 tk: Term} (plist: Eq_Trans S A t1 tk) : ℕ :=
    match plist with
    | Eq_Trans.two_trans p1 p2 => δ₂ p1 + δ₂ p2 
    | Eq_Trans.trans_trans phead plist => δ₂ phead + δ₂Trans plist
@[simp]
  def δ₂Int {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (premises: Eq_Int S A t tlist) : ℕ :=
    match premises with
    | Eq_Int.two_lists x1 x2 => δ₂ x1 + δ₂ x2 
    | Eq_Int.new_list xhead xlist => δ₂ xhead + δ₂Int xlist
end



mutual 
@[simp]
def δ₃ {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): ℕ := 
    match proof with
    | eq_ady.ax .. => 1
    | eq_ady.eq _ p => 1
    | eq_ady.cons_pair p1 p2 => 1 + δ₃ p1 + δ₃ p2
    | eq_ady.cons_enc p1 p2 => 1 + δ₃ p1 + δ₃ p2
    | eq_ady.cons_pk p => 1 + δ₃ p
    | eq_ady.sym p => 1 + δ₃ p
    | eq_ady.trans plist => 1 + δ₃Trans plist
    | eq_ady.proj_pair_left p _ => 1 +  δ₃ p
    | eq_ady.proj_pair_right p _ => 1 + δ₃ p
    | eq_ady.proj_enc_key p _ => 1 + δ₃ p
    | eq_ady.proj_enc_term p _ => 1 + δ₃ p
    | eq_ady.proj_pk p _ => 1 + δ₃ p
    | eq_ady.subst p p' => 1 + δ₃ p + δ₃ p'
    | eq_ady.prom p => 1 + δ₃ p
    | eq_ady.int premises => 1 + δ₃Int premises
    | eq_ady.wk eqa _ dylist => 1 + δ₃ eqa
@[simp]
  def δ₃Trans  {S: TermSet} {A: AssertionSet} {t1 tk: Term} (plist: Eq_Trans S A t1 tk) : ℕ :=
    match plist with
    | Eq_Trans.two_trans p1 p2 =>  δ₃ p1 + δ₃ p2 
    | Eq_Trans.trans_trans phead plist =>  δ₃ phead + δ₃Trans plist
@[simp]
  def δ₃Int {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (premises: Eq_Int S A t tlist) : ℕ :=
    match premises with
    | Eq_Int.two_lists x1 x2 =>  δ₃ x1 + δ₃ x2 
    | Eq_Int.new_list xhead xlist =>   δ₃ xhead + δ₃Int xlist
end





mutual
inductive SubProofEqEq: ∀ {S₁ S₂ A₁ A₂ a₁ a₂}, (eq_ady S₁ A₁ a₁) -> (eq_ady S₂ A₂ a₂) -> Prop
| refl {S A a}
    (pa: eq_ady S A a)
  : SubProofEqEq pa pa

| cons_pair_left {S A} {t1 t2 u1 u2: Term} (p1: eq_ady S A (Assertion.eq t1 u1)) (p2: eq_ady S A (Assertion.eq t2 u2)): SubProofEqEq p1 (eq_ady.cons_pair p1 p2)
| cons_pair_right  {S A} {t1 t2 u1 u2: Term} (p1: eq_ady S A (Assertion.eq t1 u1)) (p2: eq_ady S A (Assertion.eq t2 u2)): SubProofEqEq p2 (eq_ady.cons_pair p1 p2)

| cons_enc_term {S A} {t1 t2 : Term} {k1 k2 : Key}
    (p1:eq_ady S A (Assertion.eq t1 t2))
    (p2: eq_ady S A (Assertion.eq ((Term.key k1 )) (Term.key k2)))
  : SubProofEqEq p1 (eq_ady.cons_enc p1 p2)
| cons_enc_key {S A} {t1 t2 : Term} {k1 k2 : Key}
    (p1:eq_ady S A (Assertion.eq t1 t2))
    (p2: eq_ady S A (Assertion.eq ((Term.key k1)) (Term.key k2)))
  : SubProofEqEq p2 (eq_ady.cons_enc p1 p2)

| sym {S A} {t u: Term}
    (p: eq_ady S A (Assertion.eq t u))
  : SubProofEqEq p (eq_ady.sym p)

| trans  {S A} {a: Assertion} {t1 tk : Term}
    {p: Eq_Trans S A t1 tk}
    {pa: eq_ady S A a}
    (subp: SubProofEqTrans pa p)
  : SubProofEqEq pa (eq_ady.trans p)

| proj_pair_left {S A} {t1 t2 u1 u2 : Term}
    (p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2)))
    p'
  : SubProofEqEq p (eq_ady.proj_pair_left p p')

| proj_pair_right {S A} {t1 t2 u1 u2 : Term}
    (p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2)))
    p' :
  SubProofEqEq p (eq_ady.proj_pair_right p p')

| proj_enc_term  {S A} {k1 k2 : Key} {t1 t2 : Term}
    (p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))) 
    p'
  : SubProofEqEq p (eq_ady.proj_enc_term p p')

| proj_enc_key {S A} {k1 k2 : Key} {t1 t2 : Term}
    (p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2)))
    p'
  : SubProofEqEq p (eq_ady.proj_enc_key p p')
                 
| subst_eq {S A} {t u : Term} {l : List Term}
    (pmem: eq_ady S A (Assertion.member t l))
    (peq: eq_ady S A (Assertion.eq t u))
  : SubProofEqEq peq (eq_ady.subst pmem peq)

| subst_mem  {S A} {t u : Term} {l : List Term}
    (pmem: eq_ady S A (Assertion.member t l))
    (peq: eq_ady S A (Assertion.eq t u))
  : SubProofEqEq pmem (eq_ady.subst pmem peq)

| prom {S A} {t n : Term}
    (p: eq_ady S A (Assertion.member t [n]))
  : SubProofEqEq p (eq_ady.prom p)

| int {S A} {a: Assertion} {t: Term} {l: List Term}
    {pl: Eq_Int S A t l}
    {pa: eq_ady S A a}
    (subp: SubProofEqInt pa pl)
  : SubProofEqEq pa (eq_ady.int pl)    

| wk {S A} {t n : Term} {nlist : List Term}
    (p: eq_ady S A (Assertion.eq t n))
    (p':  n ∈ nlist)
    (p'l: Eq_Wk S nlist)
  : SubProofEqEq p (eq_ady.wk p p' p'l)



| cons_pair_left_step {S A} {t1 t2 u1 u2: Term} {p1: eq_ady S A (Assertion.eq t1 u1)} {p2: eq_ady S A (Assertion.eq t2 u2)} {p} (subp: SubProofEqEq p p1): SubProofEqEq p (eq_ady.cons_pair p1 p2)
| cons_pair_right_step {S A} {t1 t2 u1 u2: Term} {p1: eq_ady S A (Assertion.eq t1 u1)} {p2: eq_ady S A (Assertion.eq t2 u2)} {p} (subp: SubProofEqEq p p2): SubProofEqEq p (eq_ady.cons_pair p1 p2)


| cons_enc_term_step {S A} {t1 t2 : Term} {k1 k2 : Key}
    {p1:eq_ady S A (Assertion.eq t1 t2)}
    {p2: eq_ady S A (Assertion.eq ((Term.key k1 )) (Term.key k2))}
       {p} (subp: SubProofEqEq p p1)
  : SubProofEqEq p (eq_ady.cons_enc p1 p2)

| cons_enc_key_step {S A} {t1 t2 : Term} {k1 k2 : Key}
    {p1:eq_ady S A (Assertion.eq t1 t2)}
    {p2: eq_ady S A (Assertion.eq ((Term.key k1 )) (Term.key k2))}
       {p} (subp: SubProofEqEq p p2)
  : SubProofEqEq p (eq_ady.cons_enc p1 p2)


| sym_step {S A} {t u: Term}
    {p': eq_ady S A (Assertion.eq t u)}
    {p} (subp: SubProofEqEq p p')
  : SubProofEqEq p (eq_ady.sym p')

| proj_pair_left_step {S A} {t1 t2 u1 u2 : Term}
    {p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))}
    {p'}
   {ps} (subp: SubProofEqEq ps p)       
  : SubProofEqEq ps (eq_ady.proj_pair_left p p')


| proj_pair_right_step {S A} {t1 t2 u1 u2 : Term}
    {p: eq_ady S A (Assertion.eq (Term.pair t1 t2) (Term.pair u1 u2))}
    {p'}
   {ps} (subp: SubProofEqEq ps p)       
  : SubProofEqEq ps (eq_ady.proj_pair_right p p')


| proj_enc_term_step  {S A} {k1 k2 : Key} {t1 t2 : Term}
    {p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))}
    {p'}
    {ps} (subp: SubProofEqEq ps p) 
  : SubProofEqEq ps (eq_ady.proj_enc_term p p')

| proj_enc_key_step  {S A} {k1 k2 : Key} {t1 t2 : Term}
    {p: eq_ady S A (Assertion.eq (Term.enc t1 k1) (Term.enc t2 k2))}
    {p'}
    {ps} (subp: SubProofEqEq ps p) 
  : SubProofEqEq ps (eq_ady.proj_enc_key p p')
                 
| subst_eq_step {S A} {t u : Term} {l : List Term}
    {pmem: eq_ady S A (Assertion.member t l)}
    {peq: eq_ady S A (Assertion.eq t u)}
    {ps} (subp: SubProofEqEq ps peq) 
  : SubProofEqEq ps (eq_ady.subst pmem peq)

| subst_mem_step {S A} {t u : Term} {l : List Term}
    {pmem: eq_ady S A (Assertion.member t l)}
    {peq: eq_ady S A (Assertion.eq t u)}
    {ps} (subp: SubProofEqEq ps pmem) 
  : SubProofEqEq ps (eq_ady.subst pmem peq)

| prom_step {S A} {t n : Term}
    {p: eq_ady S A (Assertion.member t [n])}
    {ps} (subp: SubProofEqEq ps p) 
  : SubProofEqEq ps (eq_ady.prom p)  

| wk_step {S A} {t n : Term} {nlist : List Term}
    {p: eq_ady S A (Assertion.eq t n)}
    {p':  n ∈ nlist}
    {p'l: Eq_Wk S nlist}
    {ps} (subp: SubProofEqEq ps p)
  : SubProofEqEq ps (eq_ady.wk p p' p'l)

inductive SubProofEqTrans: ∀ {S A} {a: Assertion} {t1 tn : Term}, eq_ady S A a -> Eq_Trans S A t1 tn -> Prop
| two_trans_left {S A} {a: Assertion} {t1 t2 t3 : Term}
    (p1: eq_ady S A (Assertion.eq t1 t2))
    (p2: eq_ady S A (Assertion.eq t2 t3))
    {pa: eq_ady S A a}
    (psub: SubProofEqEq pa p1)
  : SubProofEqTrans pa (Eq_Trans.two_trans p1 p2)
                    
| two_trans_right {S A} {a: Assertion} {t1 t2 t3 : Term}
    (p1: eq_ady S A (Assertion.eq t1 t2))
    (p2: eq_ady S A (Assertion.eq t2 t3))
    {pa: eq_ady S A a}
    (psub: SubProofEqEq pa p2)
  : SubProofEqTrans pa (Eq_Trans.two_trans p1 p2)

| trans_trans_head {S A} {a: Assertion} {t1 tk tk' : Term}
    (phead: eq_ady S A (Assertion.eq t1 tk))
    (ptail: Eq_Trans S A tk tk')
    {pa: eq_ady S A a}
    (psub: SubProofEqEq pa phead)
  : SubProofEqTrans pa (Eq_Trans.trans_trans phead ptail)

| trans_trans_tail {S A} {a: Assertion} {t1 tk tk' : Term}
    (phead: eq_ady S A (Assertion.eq t1 tk))
    (ptail: Eq_Trans S A tk tk')
    {pa: eq_ady S A a}
    (psub: SubProofEqTrans pa ptail)
  : SubProofEqTrans pa (Eq_Trans.trans_trans phead ptail)

inductive SubProofEqInt : ∀ {S: TermSet} {A: AssertionSet} {a: Assertion} {t: Term} {tl: List Term}, eq_ady S A a -> Eq_Int S A t tl -> Prop
| two_lists_left {S A} {a: Assertion} {t : Term} {l1 l2: List Term}
    (p1: eq_ady S A (Assertion.member t l1))
    (p2: eq_ady S A (Assertion.member t l2))
    {pa: eq_ady S A a}
    (subp: SubProofEqEq pa p1)
  : SubProofEqInt pa (Eq_Int.two_lists p1 p2)
| two_lists_right {S A} {a: Assertion} {t : Term} {l1 l2 : List Term}
    (p1: eq_ady S A (Assertion.member t l1))
    (p2: eq_ady S A (Assertion.member t l2))
    {pa: eq_ady S A a}
    (subp: SubProofEqEq pa p2)
  : SubProofEqInt pa (Eq_Int.two_lists p1 p2)

| new_list_head {S A} {a: Assertion} {t : Term} {l1 intersect : List Term}
    (phead: eq_ady S A (Assertion.member t l1))
    (ptail: Eq_Int S A t intersect)
    {pa: eq_ady S A a}
    (subp: SubProofEqEq pa phead)
  : SubProofEqInt pa (Eq_Int.new_list phead ptail)

| new_list_tail {S A} {a: Assertion} {t : Term} {l1 intersect  : List Term}
    (phead: eq_ady S A (Assertion.member t l1))
    (ptail: Eq_Int S A t intersect)
    {pa: eq_ady S A a}
    (subp: SubProofEqInt pa ptail)
  : SubProofEqInt pa (Eq_Int.new_list phead ptail)
end


def EqAdyProofTermSet {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a) : Set Term :=
{t | ∃  (a': Assertion) (p': eq_ady S A a'), SubProofEqEq p' p ∧ AssertionMaximalSubTerm a' t}

def AssertionSetTermListSet (A: AssertionSet) : Set (List Term) :=
  {l |  ∃ (t: Term),  (Assertion.member t l) ∈ A} 

def ProofTermListSet {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a) : Set (List Term) :=
    {l| ∃ (t: Term) (p': eq_ady S A (Assertion.member t l)), SubProofEqEq p' p}

def TermSetTermListSet (S: TermSet): Set (List Term) :=
  {[t] | t ∈ S}

def Substitution := ∀ (v: Var), match v with | Var.term .. => Term | Var.key .. => Key

def isEmpty {X: Type} (S: Set  X) := ∀ x, (x ∈ S → False)

def ConcreteSubstitution (s: Substitution) :=
  forall (v: Var),
    match v with
    | Var.term v => isEmpty (FVSetTerm (s (Var.term v))) 
    | Var.key v => isEmpty (FVSetTerm (Term.key (s (Var.key v))))
    
def substkey (s: Substitution) (k: Key) : Key :=
  match k with
  | Key.var v => s (Var.key v)
  | _ => k

def apply_substition (s: Substitution) (t: Term) : Term:=
  match t with
  | Term.var v => s (Var.term v)
  | Term.name m => Term.name m
  | Term.key k => Term.key (substkey s k)
  | Term.pair t1 t2 => Term.pair (apply_substition s t1) (apply_substition s t2)
  | Term.enc t k => Term.enc (apply_substition s t) (substkey s k)
  

def Consistent (S: TermSet) (A: AssertionSet) :=
   ∃ (s: Substitution),
    ConcreteSubstitution s ->
      ((∀ t1 t2, eq_ady S A (Assertion.eq t1 t2) -> (apply_substition s t1) = (apply_substition s t2)) ∧
      (∀ t tlist, eq_ady S A (Assertion.member t tlist) ->  (apply_substition s t) ∈ tlist))


abbrev EqAdyNormalisation := ∀ {S: TermSet} {A: AssertionSet} {a: Assertion} (_: eq_ady S A a),
    Consistent S A -> ∃ (p': eq_ady S A a), isNormalEqAdy p' = true

abbrev EqAdySubTerm := ∀ {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a),
    Consistent S A ->
    isNormalEqAdy p = true ->
    let Y :=  SubTermSet S ∪ AssertionSetSubTermSet (A ∪ {a});
     EqAdyProofTermSet p ⊆  Y ∧  
     ProofTermListSet p ⊆ AssertionSetTermListSet (A ∪ {a}) ∪ TermSetTermListSet Y

/-
  motive_2 := fun {A t1 tn} (_: Eq_Trans S A t1 tn), Consistent S A → ∃ (tlist:Eq_Trans S A t1 tn ), isNormalEqTrans tlist && adjacentSafe tlist && !(containsReflexiveTrans tlist) = true
  motive_3 := fun {A t tl} (_: Eq_Int S A t tl) => ∃ (premises: Eq_Int S A t tl), Consistent S A → isNormalEqInt premises = true
  motive_4 := fun {tl} (_: Eq_Wk S tl) => ∃ (dylist: Eq_Wk S tl), isNormalEqWk dylist = true
-/

def transAppend {S: TermSet} {A: AssertionSet} {t1 t2 t3: Term} (l1: Eq_Trans S A t1 t2) (l2: Eq_Trans S A t2 t3) : Eq_Trans S A t1 t3 :=
  match l1 with
  | Eq_Trans.two_trans p1 p2 => Eq_Trans.trans_trans p1 (Eq_Trans.trans_trans p2 l2)
  | Eq_Trans.trans_trans p plist => Eq_Trans.trans_trans p (transAppend plist l2)

def transSnoc {S: TermSet} {A: AssertionSet} {t1 t2 t3: Term} (l1: Eq_Trans S A t1 t2) (l2: eq_ady S A (Assertion.eq t2 t3)) : Eq_Trans S A t1 t3 :=
  match l1 with
  | Eq_Trans.two_trans p1 p2 => Eq_Trans.trans_trans p1 (Eq_Trans.two_trans p2 l2)
  | Eq_Trans.trans_trans p plist => Eq_Trans.trans_trans p (transSnoc plist l2)

def intAppend {S: TermSet} {A: AssertionSet} {t: Term} {tlist1 tlist2: List Term} (l1: Eq_Int S A t tlist1) (l2: Eq_Int S A t tlist2) : Eq_Int S A t (intersection tlist1 tlist2) := 
  match l1 with
  | Eq_Int.two_lists p1 p2 => 
    by
      rw [← intersection_assoc]
      exact Eq_Int.new_list p1 (Eq_Int.new_list p2 l2)
  | Eq_Int.new_list phead ptail =>
    by
      rw [← intersection_assoc]
      exact Eq_Int.new_list phead (intAppend ptail l2)

def intSnoc {S: TermSet} {A: AssertionSet} {t: Term} {tlist1 tlist2: List Term} (l1: Eq_Int S A t tlist1) (l2: eq_ady S A (Assertion.member t tlist2) ) : Eq_Int S A t (intersection tlist1 tlist2) := 
  match l1 with
  | Eq_Int.two_lists p1 p2 =>
    by
      rw [← intersection_assoc]
      exact Eq_Int.new_list p1 (Eq_Int.two_lists p2 l2)
      
  | @Eq_Int.new_list _ _ _ l l' p plist => 
    by
      have : Eq_Int S A t (intersection l (intersection l' tlist2)) :=  
        Eq_Int.new_list p 
                        (by
                          -- exact transSnoc plist l2
                          sorry)
      sorry

mutual
def eqAdySymTransform {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a) : eq_ady S A a × Bool :=
  match proof with
  | eq_ady.ax S inH => (eq_ady.ax S inH, false)
  | eq_ady.eq A dyp => (eq_ady.eq A dyp, false)
  | eq_ady.cons_pair p1 p2 =>
    let res1 := eqAdySymTransform p1;
    if res1.snd 
    then (eq_ady.cons_pair res1.fst p2 , true)
    else let res2 := eqAdySymTransform p2;
         (eq_ady.cons_pair p1 res2.fst, res2.snd)
  | eq_ady.cons_enc p1 p2 =>
    let res1 := eqAdySymTransform p1;
    if res1.snd 
    then (eq_ady.cons_enc res1.fst p2 , true)
    else let res2 := eqAdySymTransform p2;
         (eq_ady.cons_enc p1 res2.fst, res2.snd)
  | eq_ady.cons_pk p =>
    let res := (eqAdySymTransform p);
           (eq_ady.cons_pk res.fst, res.snd)
  | eq_ady.sym p =>
    match p with
    | eq_ady.eq A p' => (eq_ady.eq A p', true)
    | eq_ady.sym p' => (p', true)
    | eq_ady.cons_pair p1 p2 => (eq_ady.cons_pair p1.sym p2.sym, true)
    | eq_ady.cons_enc p1 p2 => (eq_ady.cons_enc p1.sym p2.sym, true)
    | eq_ady.cons_pk p => (eq_ady.cons_pk p.sym, true)
    | eq_ady.proj_pair_left  p pin => (eq_ady.proj_pair_left p.sym sorry, true)
    | eq_ady.proj_pair_right  p pin => (eq_ady.proj_pair_right p.sym sorry, true)
    | eq_ady.proj_enc_term  p pin => (eq_ady.proj_enc_term p.sym sorry, true)
    | eq_ady.proj_enc_key  p pin => (eq_ady.proj_enc_key p.sym sorry, true)
    | eq_ady.proj_pk p pin => (eq_ady.proj_pk p.sym sorry, true)
    | eq_ady.trans plist => (eq_ady.trans (propagateSym plist), true)
    | x => let res := (eqAdySymTransform x);
           (eq_ady.sym res.fst, res.snd)
  | eq_ady.proj_pair_left p pin =>
    let res := (eqAdySymTransform p);
           (eq_ady.proj_pair_left res.fst pin, res.snd)
  | eq_ady.proj_pair_right p pin =>
    let res := (eqAdySymTransform p);
           (eq_ady.proj_pair_right res.fst pin, res.snd)
  | eq_ady.proj_enc_key p pin =>
    let res := (eqAdySymTransform p);
           (eq_ady.proj_enc_key res.fst pin, res.snd)
  | eq_ady.proj_enc_term p pin =>
    let res := (eqAdySymTransform p);
           (eq_ady.proj_enc_term res.fst pin, res.snd)
  | eq_ady.proj_pk p pin =>
    let res := (eqAdySymTransform p);
           (eq_ady.proj_pk res.fst pin, res.snd)
  | eq_ady.subst p1 p2 =>
    let res1 := eqAdySymTransform p1;
    if res1.snd 
    then (eq_ady.subst res1.fst p2 , true)
    else let res2 := eqAdySymTransform p2;
         (eq_ady.subst p1 res2.fst, res2.snd)
  | eq_ady.prom p =>
    let res := (eqAdySymTransform p);
           (eq_ady.prom res.fst, res.snd)
  | eq_ady.wk p a1 a2 =>
    let res := (eqAdySymTransform p);
           (eq_ady.wk res.fst a1 a2, res.snd)
  | eq_ady.trans plist => 
    let reslist := transSymFold plist;
    (eq_ady.trans reslist.fst, reslist.snd)
  | eq_ady.int premises =>
    let reslist := intSymFold premises;
    (eq_ady.int reslist.fst, reslist.snd)

def propagateSym {S: TermSet} {A: AssertionSet} {t1 tn: Term} (plist: Eq_Trans S A t1 tn) : Eq_Trans S A tn t1 :=
  match plist with
  | Eq_Trans.two_trans p1 p2 => Eq_Trans.two_trans (eq_ady.sym p2) (eq_ady.sym p1)
  | Eq_Trans.trans_trans p plist =>
                         match plist with
                         | Eq_Trans.two_trans p1 p2 => Eq_Trans.trans_trans p2.sym (Eq_Trans.two_trans p1.sym p.sym)
                         | Eq_Trans.trans_trans p' plist => transAppend (propagateSym plist) (Eq_Trans.two_trans p'.sym p.sym )
def transSymFold {S: TermSet} {A: AssertionSet} {t1 tn: Term} (plist: Eq_Trans S A t1 tn) : Eq_Trans S A t1 tn × Bool :=
  match plist with
  | Eq_Trans.two_trans p1 p2 =>
    let res1 := eqAdySymTransform p1;
    if res1.snd 
    then (Eq_Trans.two_trans res1.fst p2 , true)
    else let res2 := eqAdySymTransform p2;
         (Eq_Trans.two_trans p1 res2.fst, res2.snd)
  | Eq_Trans.trans_trans p plist =>
    let res := eqAdySymTransform p;
    if res.snd
    then (Eq_Trans.trans_trans res.fst plist, true)
    else let reslist := transSymFold plist;
         (Eq_Trans.trans_trans p reslist.fst, reslist.snd)
def intSymFold {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (premises: Eq_Int S A t tlist) : Eq_Int S A t tlist × Bool :=
  match premises with
  | Eq_Int.two_lists p1 p2 =>
    let res1 := eqAdySymTransform p1;
    if res1.snd 
    then (Eq_Int.two_lists res1.fst p2 , true)
    else let res2 := eqAdySymTransform p2;
         (Eq_Int.two_lists p1 res2.fst, res2.snd)
  | Eq_Int.new_list xhead xlist =>
    let res := eqAdySymTransform xhead;
    if res.snd
    then (Eq_Int.new_list res.fst xlist, true)
    else let reslist := intSymFold xlist;
         (Eq_Int.new_list xhead reslist.fst, reslist.snd)
end


mutual 
@[simp]
def δSym {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): ℕ := 
    match proof with
    | eq_ady.ax .. => 0
    | eq_ady.eq _ p => 0
    | eq_ady.cons_pair p1 p2 =>  δSym p1 + δSym p2
    | eq_ady.cons_enc p1 p2 =>  δSym p1 + δSym p2
    | eq_ady.cons_pk p => δSym p
    | eq_ady.sym p =>  δSym p + δ₃ p
    | eq_ady.trans plist =>  δSymTrans plist
    | eq_ady.proj_pair_left p _ =>  δSym p
    | eq_ady.proj_pair_right p _ =>  δSym p
    | eq_ady.proj_enc_key p _ =>  δSym p
    | eq_ady.proj_enc_term p _ =>  δSym p
    | eq_ady.proj_pk p _ =>  δSym p
    | eq_ady.subst p p' =>  δSym p + δSym p'
    | eq_ady.prom p =>  δSym p
    | eq_ady.int premises =>  δSymInt premises
    | eq_ady.wk eqa _ dylist =>  δSym eqa
@[simp]
  def δSymTrans  {S: TermSet} {A: AssertionSet} {t1 tk: Term} (plist: Eq_Trans S A t1 tk) : ℕ :=
    match plist with
    | Eq_Trans.two_trans p1 p2 =>  δSym p1 + δSym p2 
    | Eq_Trans.trans_trans phead plist =>  δSym phead + δSymTrans plist
@[simp]
  def δSymInt {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (premises: Eq_Int S A t tlist) : ℕ :=
    match premises with
    | Eq_Int.two_lists x1 x2 =>  δSym x1 + δSym x2 
    | Eq_Int.new_list xhead xlist =>  δSym xhead + δSymInt xlist
end



lemma transAppendSym: ∀ {S: TermSet} {A: AssertionSet} {t1 t2 t3: Term} {l1: Eq_Trans S A t1 t2} {l2: Eq_Trans S A t2 t3}, δSymTrans (transAppend l1 l2) = δSymTrans l1 + δSymTrans l2 :=
  by
    intros S A t1 t2 t3 l1
    induction l1 using Eq_Trans.rec (motive_1 := fun _ _ p => True) (motive_3 := fun _ _ _ _ => True) (motive_4 := fun _ _ => True)
    case two_trans p1 p2 => 
      intros l2
      simp [transAppend]
      omega
      
    case trans_trans phead plist _ plist_ih =>
      intros l2
      cases l2 with
      | two_trans p1 p2 => 
        simp [transAppend]
        specialize @plist_ih (Eq_Trans.two_trans p1 p2)
        rw [plist_ih]
        simp
        omega
        
      | trans_trans ph pl =>
        simp [transAppend]
        specialize @plist_ih (Eq_Trans.trans_trans ph pl)
        rw [plist_ih]
        simp
        omega
        
      
    all_goals (apply True.intro)


lemma breakApart : ∀{S A t2 t3} (plist: Eq_Trans S A t2 t3) {t1} (phead: eq_ady S A (Assertion.eq t1 t2)) , δSymTrans (propagateSym (Eq_Trans.trans_trans phead plist)) = δ₃ phead + δSym phead + δSymTrans (propagateSym (plist))  :=
  by
    intros S A t2 t3 plist
    induction plist using Eq_Trans.rec (motive_1 := fun _ _ p => True /- (eqAdySymTransform p).snd = Bool.true → δSym (eqAdySymTransform p).fst < δSym p-/ ) (motive_3 := fun _ _ _ _ => True) (motive_4 := fun _ _ => True)
    case two_trans p1 p2 =>
      intros t1 phead
      simp [propagateSym]
      omega
      
    case trans_trans phead' plist _ plist_ih =>
      
      intros t1' phead'
      simp [propagateSym]
      rw [transAppendSym]
      rw [plist_ih]
      simp
      omega
    all_goals (apply True.intro)
    


lemma transPropagate: ∀ {S A t1 tn } (p: Eq_Trans S A t1 tn), δSymTrans (propagateSym p) = δSymTrans p +  δ₃Trans p :=
  
  by
    intros S A t1 tn p 
    induction p using Eq_Trans.rec (motive_1 := fun _ _ p => True /- (eqAdySymTransform p).snd = Bool.true → δSym (eqAdySymTransform p).fst < δSym p-/ ) (motive_3 := fun _ _ _ _ => True) (motive_4 := fun _ _ => True)
    
    case two_trans p1 p2 =>
      simp [propagateSym]
      omega
      
    case trans_trans phead plist _ plist_ih =>
      cases plist with
      | two_trans =>
        simp [propagateSym]
        omega
        
      | trans_trans phead plist =>
        simp
        simp [propagateSym]
        simp [propagateSym] at plist_ih
        rw [transAppendSym]
        simp [propagateSym]
        rw [breakApart] at plist_ih
        omega
    all_goals (apply True.intro)
    


lemma eqAdySymTransformDecrease: ∀ {S A a} (p: eq_ady S A a), (eqAdySymTransform p).snd = Bool.true → δSym (eqAdySymTransform p).fst < δSym p  :=
  by
    
    intros S A a p
    induction p using eq_ady.rec (motive_3 := fun _ _ _ premises =>  (intSymFold premises).snd = true →  δSymInt (intSymFold premises).fst < δSymInt premises) (motive_2 := fun _ _ _ plist => (transSymFold plist).snd → δSymTrans (transSymFold plist).fst < δSymTrans plist) (motive_4 := fun _ _ => True) with
    | ax => simp [eqAdySymTransform]
    | eq => simp [eqAdySymTransform]
    | cons_pair p1 p2 p1_ih p2_ih =>
      intros h
      unfold eqAdySymTransform at h
      simp at h
      unfold eqAdySymTransform
      simp 
      cases E : (eqAdySymTransform p1).2 with
      | false =>
        simp
        rw [E] at h
        simp at h
        apply p2_ih
        exact h
        
      | true =>
        simp
        rw [E] at h
        simp at h
        apply p1_ih
        exact E
    | cons_enc p1 p2 p1_ih p2_ih =>
      intros h
      unfold eqAdySymTransform at h
      simp at h
      unfold eqAdySymTransform
      simp 
      cases E : (eqAdySymTransform p1).2 with
      | false =>
        simp
        rw [E] at h
        simp at h
        apply p2_ih
        exact h
        
      | true =>
        simp
        rw [E] at h
        simp at h
        apply p1_ih
        exact E
    | cons_pk p p_ih =>
      simp [eqAdySymTransform]
      intros h; specialize p_ih h
      exact p_ih
    | sym p p_ih =>
      intros h
      cases p
      any_goals (simp [eqAdySymTransform] <;> omega)
      case ax inH =>
        simp [eqAdySymTransform] at h
      case trans p =>
        unfold eqAdySymTransform
        simp
        rw [transPropagate]
        omega
      case prom proof =>
        simp at p_ih
        unfold eqAdySymTransform at h ; simp at h
        specialize p_ih h
        simp
        unfold eqAdySymTransform ; simp
        have this : δ₃ (eqAdySymTransform proof.prom).1 < 1 + δ₃ proof :=
          by
            simp [eqAdySymTransform]
            sorry
        
        sorry
    | trans plist p_ih =>
      intros h
      simp [eqAdySymTransform] at h
      specialize p_ih h
      simp [eqAdySymTransform]
      exact p_ih
    | proj_pair_left p _ p_ih =>
      simp [eqAdySymTransform]
      intros h; specialize p_ih h
      exact p_ih
    | proj_pair_right p _ p_ih =>
      simp [eqAdySymTransform]
      intros h; specialize p_ih h
      exact p_ih
    | proj_enc_term p _ p_ih =>
      simp [eqAdySymTransform]
      intros h; specialize p_ih h
      exact p_ih
    | proj_enc_key p _ p_ih =>
      simp [eqAdySymTransform]
      intros h; specialize p_ih h
      exact p_ih
    | proj_pk p _ p_ih =>
      simp [eqAdySymTransform]
      intros h; specialize p_ih h
      exact p_ih
    | subst proofMember proofEq proofMember_ih proofEq_ih =>
      simp [eqAdySymTransform]
      cases eqn: (eqAdySymTransform proofMember).2 with
      | true =>
        simp
        specialize (proofMember_ih eqn)
        exact proofMember_ih
      | false =>
        simp
        intros h; specialize proofEq_ih h
        exact proofEq_ih
    | prom p p_ih =>
      simp [eqAdySymTransform]
      intros h; specialize p_ih h
      exact p_ih
      
    | int premises premises_ih =>
      simp [eqAdySymTransform]
      intros h; specialize premises_ih h
      exact premises_ih
    | wk proofEq _ _ proofEq_ih _ =>
      simp [eqAdySymTransform]
      intros h; specialize proofEq_ih h
      exact proofEq_ih
      
      
    | two_trans p1 p2 p1_ih p2_ih h =>
      revert h
      simp [transSymFold] 
      cases eqn: (eqAdySymTransform p1).2 with
      | true =>
        specialize p1_ih eqn
        simp
        assumption
        
      | false =>
        simp
        intros h; specialize p2_ih h
        assumption
    | trans_trans phead plist phead_ih plist_ih h =>
      revert h
      simp [eqAdySymTransform, transSymFold]
      cases eqn:(eqAdySymTransform phead).2 with
      | true =>
        simp
        exact phead_ih eqn
        
      | false =>
        simp
        intros h; exact plist_ih h
    | new_list proof1 proof2 proof1_ih proof2_ih h =>
      revert h
      simp [eqAdySymTransform, intSymFold]
      cases eqn: (eqAdySymTransform proof1).2 with
      | true =>
        simp
        exact proof1_ih eqn
        
      | false =>
        simp
        intros h; exact proof2_ih h
    | two_lists phead plist phead_ih plist_ih h =>
      revert h
      simp [eqAdySymTransform, intSymFold]
      cases eqn: (eqAdySymTransform phead).2 with
      | true =>
        simp
        exact phead_ih eqn
        
      | false =>
        simp
        intros h; exact plist_ih h
    | single => apply True.intro
      
    | new => apply True.intro
      
def eqAdySymTransformer {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a) : eq_ady S A a :=
  if (eqAdySymTransform proof).2 then eqAdySymTransformer (eqAdySymTransform proof).1 else proof
  termination_by δSym proof
  decreasing_by 
  {
    apply eqAdySymTransformDecrease
    assumption
  }
  
    

mutual
def eqAdyProofTransform {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a) : eq_ady S A a × Bool :=
  match proof with
  | eq_ady.ax S inH => (eq_ady.ax S inH, false)
  | eq_ady.eq A dyp =>
    match dyp with
    | dy.pair p1 p2 =>
      (eq_ady.cons_pair (eq_ady.eq A p1) (eq_ady.eq A p2), true)
    | dy.senc p1 p2 =>
      (eq_ady.cons_enc (eq_ady.eq A p1) (eq_ady.eq A p2), true)
    | dy.aenc p1 p2 =>
      (eq_ady.cons_enc (eq_ady.eq A p1) (eq_ady.eq A p2), true)
    | dy.pk p =>
      (eq_ady.cons_pk (eq_ady.eq A p), true)
    | x => (eq_ady.eq A x, false)
    
  | eq_ady.cons_pair p1 p2 =>
    let res1 := eqAdyProofTransform p1;
    if res1.snd 
    then (eq_ady.cons_pair res1.fst p2 , true)
    else let res2 := eqAdyProofTransform p2;
         (eq_ady.cons_pair p1 res2.fst, res2.snd)
  | eq_ady.cons_enc p1 p2 =>
    let res1 := eqAdyProofTransform p1;
    if res1.snd 
    then (eq_ady.cons_enc res1.fst p2 , true)
    else let res2 := eqAdyProofTransform p2;
         (eq_ady.cons_enc p1 res2.fst, res2.snd)
  | eq_ady.cons_pk p =>
    let res := (eqAdyProofTransform p);
           (eq_ady.cons_pk res.fst, res.snd)
  | eq_ady.sym p =>
    let res := (eqAdyProofTransform p);
           (eq_ady.sym res.fst, res.snd)
  | eq_ady.proj_pair_left p pin =>
    let res := (eqAdyProofTransform p);
           (eq_ady.proj_pair_left res.fst pin, res.snd)
  | eq_ady.proj_pair_right p pin =>
    let res := (eqAdyProofTransform p);
           (eq_ady.proj_pair_right res.fst pin, res.snd)
  | eq_ady.proj_enc_key p pin =>
    let res := (eqAdyProofTransform p);
           (eq_ady.proj_enc_key res.fst pin, res.snd)
  | eq_ady.proj_enc_term p pin =>
    let res := (eqAdyProofTransform p);
           (eq_ady.proj_enc_term res.fst pin, res.snd)
  | eq_ady.proj_pk p pin =>
    let res := (eqAdyProofTransform p);
           (eq_ady.proj_pk res.fst pin, res.snd)
  | eq_ady.subst p1 p2 =>
    let res1 := eqAdyProofTransform p1;
    if res1.snd 
    then (eq_ady.subst res1.fst p2 , true)
    else let res2 := eqAdyProofTransform p2;
         (eq_ady.subst p1 res2.fst, res2.snd)
  | eq_ady.prom p =>
    let res := (eqAdyProofTransform p);
           (eq_ady.prom res.fst, res.snd)
  | eq_ady.wk p a1 a2 =>
    let res := (eqAdyProofTransform p);
           (eq_ady.wk res.fst a1 a2, res.snd)

  | eq_ady.trans plist =>
    let res := transRemoveRefl plist;
    if res.2 then res else
    let res := transRemoveTrans plist;
    if res.2 then (eq_ady.trans res.1, res.2) else
    let res := transJoinCons plist;
    if res.2 then res else
    let res := transProofFold plist;
    (eq_ady.trans res.1, res.2)

  | eq_ady.int premises =>
    let res := intRemoveInt premises;
    if res.2 then (eq_ady.int res.1, res.2) else
    let reslist := intProofFold premises;
    (eq_ady.int reslist.fst, reslist.snd)

def transRemoveRefl {S: TermSet} {A: AssertionSet} {t1 tn: Term} (plist: Eq_Trans S A t1 tn) : eq_ady S A (Assertion.eq t1 tn) × Bool :=
  match plist with
  | @Eq_Trans.two_trans S A t1 t2 t3 p1 p2 =>
    by
      apply dite (t1 = t2) <;> intros h
      · rw [h] ; apply (p2, true)
      · apply dite (t2 = t3) <;> intros h
        · rw [← h]; apply (p1, true)
        · apply (eq_ady.trans (Eq_Trans.two_trans p1 p2), false)
    
  | @Eq_Trans.trans_trans S A t1 tk tn phead ptail => 
    by
      apply dite (t1 = tk) <;> intros h
      · rw [h] ; apply (eq_ady.trans ptail, true)
      · let res := transRemoveReflFold phead ptail; 
        apply (eq_ady.trans res.1, res.2)

def transRemoveReflFold {S: TermSet} {A: AssertionSet} {t1 tk tn: Term} (phead: eq_ady S A (Assertion.eq t1 tk)) (plist: Eq_Trans S A tk tn): Eq_Trans S A t1 tn × Bool:=
  match plist with
  | @Eq_Trans.two_trans S A t2 t3 t4 p1 p2 =>
    by
      apply dite (t2 = t3) <;> intros h
      · rw [h] at phead; apply (Eq_Trans.two_trans phead p2, true) 
      · apply dite (t3 = t4) <;> intros h
        · rw [← h]; apply (Eq_Trans.two_trans phead p1, true)
        · apply (Eq_Trans.trans_trans phead (Eq_Trans.two_trans p1 p2), false)
    
  | @Eq_Trans.trans_trans S A t1 tk tn phead' ptail => 
    let res := (transRemoveReflFold phead' ptail);
     (Eq_Trans.trans_trans phead res.1, res.2)
def transRemoveTrans {S: TermSet} {A: AssertionSet} {t1 tn: Term} (plist: Eq_Trans S A t1 tn) : Eq_Trans S A t1 tn × Bool :=
  match plist with
  | Eq_Trans.two_trans p1 p2 => 
    match p1 with
    | eq_ady.trans premises => (transSnoc premises p2, true)
    | _ =>
      match p2 with
      | eq_ady.trans premises => (Eq_Trans.trans_trans p1 premises, true)
      | _ => (Eq_Trans.two_trans p1 p2, false)
  | Eq_Trans.trans_trans phead plist => 
    match phead with
    | eq_ady.trans premises => (transAppend premises plist, true)
    | _ =>
      let res := transRemoveTrans plist;
      (Eq_Trans.trans_trans phead res.1, res.2)


def transJoinCons {S: TermSet} {A: AssertionSet} {t1 tn: Term} (plist: Eq_Trans S A t1 tn) : eq_ady S A (Assertion.eq t1 tn) × Bool :=
  match plist with
  | Eq_Trans.two_trans p1 p2 => 
    match p1, p2 with
    | eq_ady.cons_pair t1 t2, eq_ady.cons_pair u1 u2 => 
      (eq_ady.cons_pair (eq_ady.trans (Eq_Trans.two_trans t1 u1))
                        (eq_ady.trans (Eq_Trans.two_trans t2 u2)), true)
    | eq_ady.cons_enc t1 t2, eq_ady.cons_enc u1 u2 => 
      (eq_ady.cons_enc (eq_ady.trans (Eq_Trans.two_trans t1 u1))
                        (eq_ady.trans (Eq_Trans.two_trans t2 u2)), true)
    | eq_ady.cons_pk k1, eq_ady.cons_pk k2  => 
      (eq_ady.cons_pk (eq_ady.trans (Eq_Trans.two_trans k1 k2)), true)
    | p1, p2 => (eq_ady.trans (Eq_Trans.two_trans p1 p2), false)
  | Eq_Trans.trans_trans phead ptail => 
    let res := transJoinConsFold phead ptail;
    (eq_ady.trans res.1, res.2)
def transJoinConsFold {S: TermSet} {A: AssertionSet} {t1 tk tn: Term} (phead: eq_ady S A (Assertion.eq t1 tk)) (plist: Eq_Trans S A tk tn): Eq_Trans S A t1 tn × Bool:=
  match plist with
  | Eq_Trans.two_trans p1 p2 => 
    match phead, p1 with
    | eq_ady.cons_pair t1 t2, eq_ady.cons_pair u1 u2 => 
      (Eq_Trans.two_trans (eq_ady.cons_pair (eq_ady.trans (Eq_Trans.two_trans t1 u1))
                        (eq_ady.trans (Eq_Trans.two_trans t2 u2))) p2, true)
    | eq_ady.cons_enc t1 t2, eq_ady.cons_enc u1 u2 => 
      (Eq_Trans.two_trans (eq_ady.cons_enc (eq_ady.trans (Eq_Trans.two_trans t1 u1))
                        (eq_ady.trans (Eq_Trans.two_trans t2 u2))) p2, true)
    | eq_ady.cons_pk k1, eq_ady.cons_pk k2  => 
      (Eq_Trans.two_trans (eq_ady.cons_pk (eq_ady.trans (Eq_Trans.two_trans k1 k2))) p2, true)
    | phead, p1 => match p1, p2 with
              | eq_ady.cons_pair t1 t2, eq_ady.cons_pair u1 u2 =>  (Eq_Trans.two_trans phead (eq_ady.cons_pair (eq_ady.trans (Eq_Trans.two_trans t1 u1))
                        (eq_ady.trans (Eq_Trans.two_trans t2 u2))), true)
              | eq_ady.cons_enc t1 t2, eq_ady.cons_enc u1 u2 => (Eq_Trans.two_trans phead (eq_ady.cons_enc (eq_ady.trans (Eq_Trans.two_trans t1 u1))
                        (eq_ady.trans (Eq_Trans.two_trans t2 u2))), true)
              | eq_ady.cons_pk k1, eq_ady.cons_pk k2  => (Eq_Trans.two_trans phead (eq_ady.cons_pk (eq_ady.trans (Eq_Trans.two_trans k1 k2))), true)
              | p1, p2 => (Eq_Trans.trans_trans phead (Eq_Trans.two_trans p1 p2), false)
  | Eq_Trans.trans_trans p1 plist => 
    match phead, p1 with
    | eq_ady.cons_pair t1 t2, eq_ady.cons_pair u1 u2 => 
      (Eq_Trans.trans_trans (eq_ady.cons_pair (eq_ady.trans (Eq_Trans.two_trans t1 u1))
                        (eq_ady.trans (Eq_Trans.two_trans t2 u2))) plist, true)
    | eq_ady.cons_enc t1 t2, eq_ady.cons_enc u1 u2 => 
      (Eq_Trans.trans_trans (eq_ady.cons_enc (eq_ady.trans (Eq_Trans.two_trans t1 u1))
                        (eq_ady.trans (Eq_Trans.two_trans t2 u2))) plist, true)
    | eq_ady.cons_pk k1, eq_ady.cons_pk k2  => 
      (Eq_Trans.trans_trans (eq_ady.cons_pk (eq_ady.trans (Eq_Trans.two_trans k1 k2))) plist, true)
    | phead, p1 =>
      let res := transJoinConsFold p1 plist;
      (Eq_Trans.trans_trans phead res.1, res.2)
      
    
def transProofFold {S: TermSet} {A: AssertionSet} {t1 tn: Term} (plist: Eq_Trans S A t1 tn) : Eq_Trans S A t1 tn × Bool :=
  match plist with
  | Eq_Trans.two_trans p1 p2 =>
    let res1 := eqAdyProofTransform p1;
    if res1.snd 
    then (Eq_Trans.two_trans res1.fst p2 , true)
    else let res2 := eqAdyProofTransform p2;
         (Eq_Trans.two_trans p1 res2.fst, res2.snd)
  | Eq_Trans.trans_trans p plist =>
    let res := eqAdyProofTransform p;
    if res.snd
    then (Eq_Trans.trans_trans res.fst plist, true)
    else let reslist := transProofFold plist;
         (Eq_Trans.trans_trans p reslist.fst, reslist.snd)

def intRemoveInt {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (plist: Eq_Int S A t tlist) : Eq_Int S A t tlist × Bool :=
  match plist with
  | Eq_Int.two_lists p1 p2 =>
    match p1 with
    | eq_ady.int premises => (intSnoc premises p2, true)
    | _ =>
      match p2 with
      | eq_ady.int premises => (Eq_Int.new_list p1 premises, true)
      | _ => (Eq_Int.two_lists p1 p2, false)
  | Eq_Int.new_list phead plist => 
    match phead with
    | eq_ady.int premises => (intAppend premises plist, true)
    | _ =>
      let res := intRemoveInt plist;
      (Eq_Int.new_list phead res.1, res.2)

def intWk {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (plist: Eq_Int S A t tlist) : eq_ady S A (Assertion.member t tlist) × Bool :=
  match plist with
  | Eq_Int.two_lists p1 p2 =>
    match p1 with
    | eq_ady.wk proofeq _ premises => sorry -- (intSnoc premises p2, true)
    | _ =>
      match p2 with
      | eq_ady.int premises => sorry -- (Eq_Int.new_list p1 premises, true)
      | _ => sorry -- (Eq_Int.two_lists p1 p2, false)
  | Eq_Int.new_list phead plist => 
    match phead with
    | eq_ady.int premises => sorry --(intAppend premises plist, true)
    | _ =>
      let res := intRemoveInt plist;
      sorry -- (Eq_Int.new_list phead res.1, res.2)

def intProofFold {S: TermSet} {A: AssertionSet} {t: Term} {tlist: List Term} (premises: Eq_Int S A t tlist) : Eq_Int S A t tlist × Bool :=
  match premises with
  | Eq_Int.two_lists p1 p2 =>
    let res1 := eqAdyProofTransform p1;
    if res1.snd 
    then (Eq_Int.two_lists res1.fst p2 , true)
    else let res2 := eqAdyProofTransform p2;
         (Eq_Int.two_lists p1 res2.fst, res2.snd)
  | Eq_Int.new_list xhead xlist =>
    let res := eqAdyProofTransform xhead;
    if res.snd
    then (Eq_Int.new_list res.fst xlist, true)
    else let reslist := intProofFold xlist;
         (Eq_Int.new_list xhead reslist.fst, reslist.snd)

def projCollapse {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a) (proj_proof: isProj proof = true) : eq_ady S A a × Bool := 
  by
    cases proof
    any_goals (simp at proj_proof)
    case proj_pair_left pin p =>
      match p with
      | eq_ady.cons_pair p1 p2 => exact (p1, true)
      | p => exact (eq_ady.proj_pair_left p pin, false)
    case proj_pair_right pin p =>
      match p with
      | eq_ady.cons_pair p1 p2 => exact (p2, true)
      | p => exact (eq_ady.proj_pair_right p pin, false)
    case proj_enc_term pin p =>
      match p with
      | eq_ady.cons_enc p1 p2 => exact (p1, true)
      | p => exact (eq_ady.proj_enc_term p pin, false)
    case proj_enc_key pin p =>
      match p with
      | eq_ady.cons_enc p1 p2 => exact (p2, true)
      | p => exact (eq_ady.proj_enc_key p pin, false)
    case proj_pk pin p =>
      match p with
      | eq_ady.cons_pk p => exact (p, true)
      | p => exact (eq_ady.proj_pk p pin, false)

def projTrans {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a) (proj_proof: isProj proof = true) : eq_ady S A a × Bool :=
  by
    cases proof
    any_goals (simp at proj_proof)
    case proj_pair_left pin p =>
      match p with
      | eq_ady.trans plist =>    
        sorry
      | p => exact (eq_ady.proj_pair_left p pin, false)
      
    all_goals sorry

def recursor {S A t1 u1 t2 u2} : Eq_Trans S A (t1.pair t2) (u1.pair u2) -> 
        Option (
          (EX fun x1 => EX fun x2 => 
              eq_ady S A (Assertion.eq t1 x1) × (eq_ady S A (Assertion.eq (x1.pair x2) (u1.pair u2)))) ⊕  
          (EX fun x1 => EX fun x2 => 
              eq_ady S A (Assertion.eq (t1.pair t2) (x1.pair x2)) × eq_ady S A (Assertion.eq x1 u1)) ⊕ 
          (EX fun x1 => EX fun x2 => EX fun y1 => EX fun y2 => 
              eq_ady S A (Assertion.eq (t1.pair t2) (x1.pair x2)) × eq_ady S A (Assertion.eq x1 y1) × eq_ady S A (Assertion.eq (y1.pair y2) (u1.pair u2))) ⊕ 
          (EX fun x1 => EX fun x2 => 
              eq_ady S A (Assertion.eq t1 x1) ×  Eq_Trans S A (x1.pair x2) (u1.pair u2)) ⊕  
          (EX fun x1 => EX fun x2 => 
              Eq_Trans S A (t1.pair t2) (x1.pair x2) × eq_ady S A (Assertion.eq x1 u1)) ⊕ 
          (EX fun x1 => EX fun x2 => EX fun y1 => EX fun y2 => 
              Eq_Trans S A (t1.pair t2) (x1.pair x2) × eq_ady S A (Assertion.eq x1 y1) × eq_ady S A (Assertion.eq (y1.pair y2) (u1.pair u2))) ⊕ 
          (EX fun x1 => EX fun x2 => EX fun y1 => EX fun y2 => 
              eq_ady S A (Assertion.eq (t1.pair t2) (x1.pair x2)) × eq_ady S A (Assertion.eq x1 y1) ×  Eq_Trans S A (y1.pair y2) (u1.pair u2)) ⊕
          (EX fun x1 => EX fun x2 => EX fun y1 => EX fun y2 => 
              Eq_Trans S A (t1.pair t2) (x1.pair x2) × eq_ady S A (Assertion.eq x1 y1) ×  Eq_Trans S A (y1.pair y2) (u1.pair u2))
        ) :=
          by
            intros p
            cases p with
            | @two_trans _ _ x _ p1 p2 => 
              match p1 with
              | @eq_ady.cons_pair _ _ _ _ x1 x2 a b =>
                apply Option.some
                apply Sum.inl
                apply EX.intro x1
                apply EX.intro x2
                apply (a, p2)
              | p1 =>
              match p2 with
              | @eq_ady.cons_pair _ _ x1 x2 _ _ a b =>
                apply Option.some; apply Sum.inr; apply Sum.inl
                apply EX.intro x1
                apply EX.intro x2
                apply (p1, a)
                
              | _ => apply Option.none
              
            | trans_trans phead plist =>
              match phead with
              | @eq_ady.cons_pair _ _ _ _ x1 x2 a b =>
                apply Option.some
                apply Sum.inr; apply Sum.inr; apply Sum.inr; apply Sum.inl
                apply EX.intro x1
                apply EX.intro x2
                apply (a, plist)
                
              | phead =>
                match (recursor plist) with
                | _ => sorry
end


def ProofMeasure := ℕ × ℕ × ℕ
def δ {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): ProofMeasure :=
  (δ₁ proof, δ₂ proof, δ₃ proof)

instance : LE ProofMeasure where
  le := fun t1 t2 =>
            (t1.1 ≤ t2.1) ∨ (t1.2.1 ≤ t2.2.1) ∨ (t1.2.2 ≤ t2.2.2)
instance : LT ProofMeasure where
  lt := fun t1 t2 =>
            t1 ≤ t2 ∧ ¬(t1 = t2)

theorem eqAdyProofTransformDecrease :  ∀ {S A a} (p: eq_ady S A a), (eqAdyProofTransform p).snd = Bool.true → δ (eqAdyProofTransform p).fst < δ p :=
  by
    intros S A a p t
    sorry
theorem Normality: EqAdyNormalisation :=
   by
     unfold EqAdyNormalisation
     intros S A a x cons
     induction x using eq_ady.rec (motive_2 := fun {A t1 tn} (_: Eq_Trans S A t1 tn) => Consistent S A → ∃ (tlist:Eq_Trans S A t1 tn ), isNormalEqTrans tlist && adjacentSafe tlist && !(containsReflexiveTrans tlist) = true) (motive_3 := fun {A t tl} (_: Eq_Int S A t tl) => ∃ (premises: Eq_Int S A t tl), Consistent S A → isNormalEqInt premises = true)  (motive_4 := fun {tl} (_: Eq_Wk S tl) => ∃ (dylist: Eq_Wk S tl), isNormalEqWk dylist = true) with
     | ax proof =>
       exists eq_ady.ax S proof 
     | eq A' proof => 
       -- I don't see how this can be proven without explicitly specifying an algorithm. Maybe we
       -- add lemmas like "all dy proofs have one destructor" which may get the proof to go through
       -- for this branch, but multiple other rewrite rules take a similar approach of "propagating"
       -- the rule upwards, including R9 involving trans, which has a lot of conditions imposed on it.
       sorry
      
     | _ => sorry
       
    
    

import Mathlib

inductive TermVar
| cons : Nat -> TermVar

inductive KeyVar
| cons : Nat  -> KeyVar

inductive Name
| cons : Nat -> Name

def Var := Sum TermVar KeyVar


inductive Key: Type
| priv (k: Name)
| pub (k: Name)
| var (v: KeyVar)

inductive Term: Type
| var (v: TermVar)
| name (m: Name)
| key (k: Key)
| pair (t1 t2: Term)
| enc (t: Term) (k: Key)

abbrev TermSet := Set Term

def FVSetTerm : Term -> Set Var
| Term.var v => {Sum.inl v}
| Term.name _ => ∅ 
| Term.key (Key.var v) => {Sum.inr v}
| Term.key _ => ∅
| Term.pair t1 t2 =>  FVSetTerm t1 ∪ FVSetTerm t2
| Term.enc t' k => (FVSetTerm t') ∪
                           match k with 
                             | Key.var v => {Sum.inr v} 
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

-- def isNormal {X: TermSet} {t: Term} (proof: dy X t): Bool :=
--   by
--     cases proof with

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




@[simp]
def isNormal {X: TermSet} {t: Term} (proof: dy X t): Bool :=
    match proof with
    | dy.ax _ =>  true
    | dy.pk kH =>  (isNormal kH)
    | dy.splitL splitH =>            
                    match splitH with
                    | dy.ax _ =>  true
                    | dy.splitL splitH =>  isNormal splitH 
                    | dy.splitR splitH =>  isNormal splitH
                    | dy.sdec kH encH =>  isNormal kH && isNormal encH
                    | dy.adec kH encH =>  isNormal kH && isNormal encH
                    | dy.pair _ _ =>  false
    | dy.splitR splitH =>            
                    match splitH with
                    | dy.ax _ =>  true
                    | dy.splitL splitH =>  isNormal splitH 
                    | dy.splitR splitH =>  isNormal splitH
                    | dy.sdec kH encH =>  isNormal kH && isNormal encH
                    | dy.adec kH encH =>  isNormal kH && isNormal encH
                    | dy.pair _ _ =>  false
    | dy.pair tH uH =>  isNormal tH && isNormal uH
    | dy.senc tH kH =>  isNormal tH && isNormal kH
    | dy.aenc tH kH =>  isNormal tH && isNormal kH
    | dy.sdec encH kH => isNormal kH &&
                      match encH with
                      | dy.ax _ =>  true
                      | dy.splitL splitH =>  isNormal splitH 
                      | dy.splitR splitH =>  isNormal splitH
                      | dy.sdec kH encH =>  isNormal kH && isNormal encH
                      | dy.adec kH encH =>  isNormal kH && isNormal encH
                      | dy.senc _ _ =>  false
    | dy.adec encH kH => isNormal kH &&
                      match encH with
                      | dy.ax _ =>  true
                      | dy.splitL splitH =>  isNormal splitH 
                      | dy.splitR splitH =>  isNormal splitH
                      | dy.sdec kH encH =>  isNormal kH && isNormal encH
                      | dy.adec kH encH =>  isNormal kH && isNormal encH
                      | dy.aenc _ _ =>  false
@[simp]
def dyProofMeasure {X: TermSet} {t: Term} (proof: dy X t): Nat := 
      1 +
      match proof with
      | dy.ax _ =>  1
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
         

-- theorem rewriterFixpoint: ∀ {X: TermSet} {t: Term} (p: dy X t),∃ (n: Nat), repeat_apply n recursiveDyProofRewriter p = 
-- repeat_apply (n + 1) recursiveDyProofRewriter p :=
--   by
--     intros X t p
--     induction p with
--     | ax inH =>
--          apply Exists.intro 0
--          simp

--     | pk kH kH_iH =>
--          cases kH_iH with
--          | intro x iHx =>
--            rw [repeatRight] at iHx
--            apply Exists.intro x
--            rw [repeatRight]
--            simp
--            sorry
    
--          -- cases kH_iH with
--          -- | intro x xH =>
--          --   apply Exists.intro (x + 1)
--          --   rw [repeatRight, repeatRight]
--          --   simp
--          --   simp at xH
--          --   sorry
--     | splitL splitH splitH_ih =>
--              simp
--              sorry
--     | _ => sorry
theorem rewriterNormaliser: ∀ {X: TermSet} {t: Term} (p p': dy X t), RewriteBigStep p p' → NormalProof p' :=
  by
    intros X t p p' RW
    induction RW 
    any_goals (constructor <;> assumption)
    all_goals (assumption)

theorem rewriteCompute: ∀ {X: TermSet} {t: Term} (p: dy X t), RewriteBigStep p (recursiveDyProofRewriter p) :=
  by
    intros X t p
    induction p with
    | ax => simp ; constructor
    | pair => simp ; constructor <;> assumption
    | senc => simp ; constructor <;> assumption
    | aenc => simp ; constructor <;> assumption
    | pk => simp ; constructor; assumption
    | splitL =>
      
      sorry

      
    | _ => sorry
      

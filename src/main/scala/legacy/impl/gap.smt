; Translation of a single path in A1 (second case) into a verification
; condition in Z3 (SMTLIB2 standard)

; This is an inductive proof.
; 
; Induction hypothesis (A1=A=G) and induction variables (i+j, n)
; must come from higher-level reasoning since SMT does not support those
; Lambda expressions for R are unrolled in the application of A1.
; 
; The bottom of the unrolled expressions in A1 are assumed to be the 
; uninterpreted function G (the requirement on R for this to be correct
; is not easily expressed but needs be included in the induction argument.)

(set-option :produce-models true)
(define-fun min2 ((x1 Int) (x2 Int)) Int
            (ite (<= x1 x2) x1 x2))

(declare-const k Int)
(declare-const n Int)
(assert (> k 0))
(assert (= n (* 2 k)))

(declare-const i Int)
(declare-const j Int)
(declare-const oi Int)
(declare-const oj Int)
(declare-fun w (Int Int) Int)
(declare-fun R (Int Int) Int)

; use in hypothesis
(declare-fun G (Int Int) Int)

(assert (>= i 0))
(assert (< i n))
(assert (>= j 0))
(assert (< j n))

; prove A1 = A assuming A1 = A = G on lower size tables

; pick second branch
(assert (< i k))
(assert (>= j k))

; actual value
(declare-const A Int)
(assert (<= A (R i j)))
(assert (forall ((q Int)) (=> (and (>= q 0) (< q j)) 
            (<= A (+ (G (+ i oi) (+ q oj)) (w (+ q oj) (+ j oj)))))))
(assert (forall ((p Int)) (=> (and (>= p 0) (< p i))
            (<= A (+ (G (+ p oi) (+ j oj)) (w (+ i oi) (+ p oi)))))))
(assert (or 
      (= A (R i j))
      (exists ((q Int)) (and (and (>= q 0) (< q j)) 
            (= A (+ (G (+ i oi) (+ q oj)) (w (+ q oj) (+ j oj))))))
      (exists ((p Int)) (and (and (>= p 0) (< p i))
            (= A (+ (G (+ p oi) (+ j oj)) (w (+ i oi) (+ p oi))))))))

; unroll definition of A on the quadrant assuming A1 = A
(declare-const j1 Int)
(assert (= j1 (- j k)))

; compute R1 call R1(i, j1)
(declare-const R1 Int)
(declare-const oj1 Int)
(assert (= oj1 (+ oj k)))

(declare-const A1 Int)
(assert (<= A1 R1))
(assert (forall ((q Int)) (=> (and (>= q 0) (< q j1)) 
            (<= A1 (+ (G (+ i oi) (+ q oj1)) (w (+ q oj1) (+ j1 oj1)))))))
(assert (forall ((p Int)) (=> (and (>= p 0) (< p i))
            (<= A1 (+ (G (+ p oi) (+ j1 oj1)) (w (+ i oi) (+ p oi)))))))
(assert (or 
      (= A1 R1)
      (exists ((q Int)) (and (and (>= q 0) (< q j1)) 
            (= A1 (+ (G (+ i oi) (+ q oj1)) (w (+ q oj1) (+ j1 oj1))))))
      (exists ((p Int)) (and (and (>= p 0) (< p i))
            (= A1 (+ (G (+ p oi) (+ j1 oj1)) (w (+ i oi) (+ p oi))))))))

; compute B2 call B2(i, j1, oi, oj, n, n/2)
(declare-const B2 Int)
(assert (= R1 (min2 
                       (R i (+ j1 k))
                       B2)))
(assert (forall ((q Int)) (=> (and (>= q 0) (< q k))
                            (<= B2 (+ (G (+ i oi) (+ q oj)) (w (+ q oj) (+ j1 oj k)))))))
(assert (exists ((q Int)) (and (>= q 0) (< q k)
                             (= B2 (+ (G (+ i oi) (+ q oj)) (w (+ q oj) (+ j1 oj k)))))))
    

; check for counter example
(assert (not (= A A1)))

(check-sat)
; (get-model)
; vim: set filetype=lisp spell :

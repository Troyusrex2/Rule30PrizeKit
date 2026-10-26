; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun x1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 32))
(declare-fun x3 () (_ BitVec 32))
(declare-fun x4 () (_ BitVec 32))
(declare-fun x5 () (_ BitVec 32))
(declare-fun x6 () (_ BitVec 32))
(declare-fun x7 () (_ BitVec 32))
(declare-fun x8 () (_ BitVec 32))
(declare-fun x9 () (_ BitVec 32))
(declare-fun x10 () (_ BitVec 32))
(declare-fun x11 () (_ BitVec 32))
(declare-fun x12 () (_ BitVec 32))
(declare-fun x13 () (_ BitVec 32))
(declare-fun x14 () (_ BitVec 32))
(declare-fun x15 () (_ BitVec 32))
(declare-fun x16 () (_ BitVec 32))
(declare-fun x17 () (_ BitVec 32))
(declare-fun x18 () (_ BitVec 32))
(declare-fun x19 () (_ BitVec 32))
(declare-fun h0 () Int)
(declare-fun h32 () Int)
(declare-fun lo () Int)
(declare-fun h1 () Int)
(declare-fun h2 () Int)
(declare-fun h3 () Int)
(declare-fun h4 () Int)
(declare-fun h5 () Int)
(declare-fun h6 () Int)
(declare-fun h7 () Int)
(declare-fun h8 () Int)
(declare-fun h9 () Int)
(declare-fun h10 () Int)
(declare-fun h11 () Int)
(declare-fun h12 () Int)
(declare-fun h13 () Int)
(declare-fun h14 () Int)
(declare-fun h15 () Int)
(declare-fun h16 () Int)
(declare-fun h17 () Int)
(declare-fun h18 () Int)
(declare-fun h19 () Int)
(declare-fun h20 () Int)
(declare-fun h21 () Int)
(declare-fun h22 () Int)
(declare-fun h23 () Int)
(declare-fun h24 () Int)
(declare-fun h25 () Int)
(declare-fun h26 () Int)
(declare-fun h27 () Int)
(declare-fun h28 () Int)
(declare-fun h29 () Int)
(declare-fun h30 () Int)
(declare-fun h31 () Int)
(assert
 (= (ext_rotate_right x0 (_ bv1 32)) (bvxor x0 (bvor (_ bv0 32) (_ bv0 32)))))
(assert
 (= (ext_rotate_right x1 (_ bv1 32)) (bvxor x1 (bvor x0 (_ bv0 32)))))
(assert
 (= (ext_rotate_right x2 (_ bv1 32)) (bvxor x2 (bvor x1 x0))))
(assert
 (= (ext_rotate_right x3 (_ bv1 32)) (bvxor x3 (bvor x2 x1))))
(assert
 (= (ext_rotate_right x4 (_ bv1 32)) (bvxor x4 (bvor x3 x2))))
(assert
 (= (ext_rotate_right x5 (_ bv1 32)) (bvxor x5 (bvor x4 x3))))
(assert
 (= (ext_rotate_right x6 (_ bv1 32)) (bvxor x6 (bvor x5 x4))))
(assert
 (= (ext_rotate_right x7 (_ bv1 32)) (bvxor x7 (bvor x6 x5))))
(assert
 (= (ext_rotate_right x8 (_ bv1 32)) (bvxor x8 (bvor x7 x6))))
(assert
 (= (ext_rotate_right x9 (_ bv1 32)) (bvxor x9 (bvor x8 x7))))
(assert
 (= (ext_rotate_right x10 (_ bv1 32)) (bvxor x10 (bvor x9 x8))))
(assert
 (let ((?x153 (bvxor x11 (bvor x10 x9))))
 (= (ext_rotate_right x11 (_ bv1 32)) ?x153)))
(assert
 (= (ext_rotate_right x12 (_ bv1 32)) (bvxor x12 (bvor x11 x10))))
(assert
 (= (ext_rotate_right x13 (_ bv1 32)) (bvxor x13 (bvor x12 x11))))
(assert
 (= (ext_rotate_right x14 (_ bv1 32)) (bvxor x14 (bvor x13 x12))))
(assert
 (= (ext_rotate_right x15 (_ bv1 32)) (bvxor x15 (bvor x14 x13))))
(assert
 (= (ext_rotate_right x16 (_ bv1 32)) (bvxor x16 (bvor x15 x14))))
(assert
 (= (ext_rotate_right x17 (_ bv1 32)) (bvxor x17 (bvor x16 x15))))
(assert
 (= (ext_rotate_right x18 (_ bv1 32)) (bvxor x18 (bvor x17 x16))))
(assert
 (= (ext_rotate_right x19 (_ bv1 32)) (bvxor x19 (bvor x18 x17))))
(assert
 (and (distinct (ext_rotate_right x19 (_ bv8 32)) x19) true))
(assert
 (= h0 0))
(assert
 (= h32 0))
(assert
 (>= lo (- 2)))
(assert
 (<= lo 0))
(assert
 (= h1 (+ h0 (ite (= ((_ extract 0 0) x19) (_ bv0 1)) 1 0))))
(assert
 (= h2 (+ h1 (ite (= ((_ extract 1 1) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h3 (+ h2 (ite (= ((_ extract 2 2) x19) (_ bv0 1)) 1 0))))
(assert
 (= h4 (+ h3 (ite (= ((_ extract 3 3) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h5 (+ h4 (ite (= ((_ extract 4 4) x19) (_ bv0 1)) 1 0))))
(assert
 (= h6 (+ h5 (ite (= ((_ extract 5 5) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h7 (+ h6 (ite (= ((_ extract 6 6) x19) (_ bv0 1)) 1 0))))
(assert
 (= h8 (+ h7 (ite (= ((_ extract 7 7) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h9 (+ h8 (ite (= ((_ extract 8 8) x19) (_ bv0 1)) 1 0))))
(assert
 (= h10 (+ h9 (ite (= ((_ extract 9 9) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h11 (+ h10 (ite (= ((_ extract 10 10) x19) (_ bv0 1)) 1 0))))
(assert
 (= h12 (+ h11 (ite (= ((_ extract 11 11) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h13 (+ h12 (ite (= ((_ extract 12 12) x19) (_ bv0 1)) 1 0))))
(assert
 (= h14 (+ h13 (ite (= ((_ extract 13 13) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h15 (+ h14 (ite (= ((_ extract 14 14) x19) (_ bv0 1)) 1 0))))
(assert
 (= h16 (+ h15 (ite (= ((_ extract 15 15) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h17 (+ h16 (ite (= ((_ extract 16 16) x19) (_ bv0 1)) 1 0))))
(assert
 (= h18 (+ h17 (ite (= ((_ extract 17 17) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h19 (+ h18 (ite (= ((_ extract 18 18) x19) (_ bv0 1)) 1 0))))
(assert
 (= h20 (+ h19 (ite (= ((_ extract 19 19) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h21 (+ h20 (ite (= ((_ extract 20 20) x19) (_ bv0 1)) 1 0))))
(assert
 (= h22 (+ h21 (ite (= ((_ extract 21 21) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h23 (+ h22 (ite (= ((_ extract 22 22) x19) (_ bv0 1)) 1 0))))
(assert
 (= h24 (+ h23 (ite (= ((_ extract 23 23) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h25 (+ h24 (ite (= ((_ extract 24 24) x19) (_ bv0 1)) 1 0))))
(assert
 (= h26 (+ h25 (ite (= ((_ extract 25 25) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h27 (+ h26 (ite (= ((_ extract 26 26) x19) (_ bv0 1)) 1 0))))
(assert
 (= h28 (+ h27 (ite (= ((_ extract 27 27) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h29 (+ h28 (ite (= ((_ extract 28 28) x19) (_ bv0 1)) 1 0))))
(assert
 (= h30 (+ h29 (ite (= ((_ extract 29 29) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (= h31 (+ h30 (ite (= ((_ extract 30 30) x19) (_ bv0 1)) 1 0))))
(assert
 (= h32 (+ h31 (ite (= ((_ extract 31 31) x19) (_ bv0 1)) (- 1) 0))))
(assert
 (>= h0 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h0 ?x546)))
(assert
 (>= h1 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h1 ?x546)))
(assert
 (>= h2 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h2 ?x546)))
(assert
 (>= h3 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h3 ?x546)))
(assert
 (>= h4 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h4 ?x546)))
(assert
 (>= h5 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h5 ?x546)))
(assert
 (>= h6 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h6 ?x546)))
(assert
 (>= h7 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h7 ?x546)))
(assert
 (>= h8 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h8 ?x546)))
(assert
 (>= h9 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h9 ?x546)))
(assert
 (>= h10 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h10 ?x546)))
(assert
 (>= h11 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h11 ?x546)))
(assert
 (>= h12 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h12 ?x546)))
(assert
 (>= h13 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h13 ?x546)))
(assert
 (>= h14 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h14 ?x546)))
(assert
 (>= h15 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h15 ?x546)))
(assert
 (>= h16 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h16 ?x546)))
(assert
 (>= h17 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h17 ?x546)))
(assert
 (>= h18 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h18 ?x546)))
(assert
 (>= h19 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h19 ?x546)))
(assert
 (>= h20 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h20 ?x546)))
(assert
 (>= h21 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h21 ?x546)))
(assert
 (>= h22 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h22 ?x546)))
(assert
 (>= h23 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h23 ?x546)))
(assert
 (>= h24 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h24 ?x546)))
(assert
 (>= h25 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h25 ?x546)))
(assert
 (>= h26 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h26 ?x546)))
(assert
 (>= h27 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h27 ?x546)))
(assert
 (>= h28 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h28 ?x546)))
(assert
 (>= h29 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h29 ?x546)))
(assert
 (>= h30 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h30 ?x546)))
(assert
 (>= h31 lo))
(assert
 (let ((?x546 (+ lo 2)))
 (<= h31 ?x546)))
(assert
 (>= h32 lo))
(assert
 (let ((?x546 (+ lo 2)))
(<= h32 ?x546)))
(check-sat)

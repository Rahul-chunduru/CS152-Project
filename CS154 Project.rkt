#lang racket
(struct hold(l r) #:transparent)
(define k 8.0)
(define limit 50)
(define VOLT 25)
(define optimum 30)
;;element-i --- gives i'th element of a list
(define (element-i l i)
  (define (help count l)
    (if (= count i) (car l) (help (+ count 1) (cdr l))))
  (help 0 l))

;;divid --- divides each element of list by its i'th element
(define (divid l i)
  (map (lambda(x) (/ x (element-i l i))) l))

;;simple-list----returns l2 after making i'th element 0 by substracting l1 from it
(define (simple-list l1 l2 i)
  (let((k (element-i l2 i)))
    (define (help l1 l2)
      (if (or (null? l1) (null? l2)) '()
          (cons (- (car l2) (* k (car l1))) (help (cdr l1) (cdr l2)))))
    (help l1 l2)))

;;column-ech --- converts i'th column into echeleon form i.e [i'th column = (1 0 0 0..)]
(define (column-ech l i) 
  (define (helper lis l)    
    (if (null? l) "does not exist" 
        (if (= (element-i (car l) i) 0) (helper (cons (car l) lis) (cdr l))
            (let((k (divid (car l) i)))
              (append (list k) lis (map (lambda(x) (simple-list k x i)) (cdr l)))))))
  (helper '() l))

;;row-echleon-form --- gives row echleon form of a matrix 
(define (row-echleon-form l)
  (define len (length l))
  (define (helper l list i)
    (let((f (column-ech l i)))
      (if (= i (- len 1))
          (append (map (lambda(x) (simple-list (car f) x i)) (reverse list)) f)
          (let  ((g (car (column-ech (cdr f) (+ i 1)))))
            (helper (cdr f) (map (lambda(x) (simple-list g x (+ i 1))) (cons (car f) list)) (+ i 1))))))
  (helper l '() 0))

;;lin-eqs-sol --- gives the solution of the given linear equations
(define (lin-eqs-sol l)
  (let ((k (length (car l))))
    (map (lambda(x) (element-i x (- k 1))) (row-echleon-form l))))

;;N-1 degree polynomial passing through N points.
(define (mod-pow n x)
  (cond ((=  n 1) x)
        ((even? n) (let (( y (mod-pow (/ n 2) x)))
                     (* y y)))
        ((odd? n) (let((z (mod-pow (/ (- n 1) 2) x)))
                    ( * z z x)))))
(define (pow n)
  (lambda(x)
    (if (= n 0) 1
        (if (< n 0) (( pow (* -1 n)) (/ 1 x))
            (mod-pow  n x)))))
(define (a-create-linear L );;gives the co-effs of the polynomial equation 
  (define n (length L))
  (define (f L)
    (define (helper i l)
       (if (= i n) l
           (helper (+ i 1) ( cons (( pow i) (car L)) l))))
    (helper 0 (cdr L)))
  (map f L))

 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;      
;;;;;;;;;;;      CIRCUIT OBJECTS     ;;;;;;;;

(define (update l l1 l2 n)
(define a (car l1)) (define b (cadr l1))
(define c (car l2)) (define d (cadr l2))
(define	x (get-field a l)) (define y  (get-field b l))
(define (update r)
   (let ((p (if (eq? r 'x) x y))
     	(t ( if (eq? r 'x) #t #f)))
	(begin (cond (( = p c) (if t (set-field! a l a) (set-field! b l a)))
      	(( = p d) (if t (set-field! a l b) (set-field! b l b)))
       	(( < p c) (if t (set-field! a l (+ p n)) (set-field! b l (+ p n))))
      	(( > p d) (if t (set-field! a l (+ p (- n 2))) (set-field! b l (+ p (- n 2)))))
      	(else (if t (set-field! a l (+ p (- n 1))) (set-field! b l (+ p (- n 1)))))))))
	(begin  (update 'x) (update 'y)))
(define (list-update l   l1 l2 n)
  (if ( < ( cadr l2) (car l2)) (list-update l l1 (reverse l2) n)
  (map	(lambda(t) (begin ( update t l1 l2 n) t))	l)))
(define (okay x y)
  (if (< (abs (- x y)) 1) #t #f))
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (remove i l)
  (cond (( = i 0) l)
	(( = i 1) (cdr l))
  	((null? l) "out of range")
  	(else (cons (car l) ( remove (- i 1) (cdr l))))))
;;;;;;;;;;;;;;
(define (generate-simpler V   garbage)
  (define n ( vector-length V))
  (define l (+ 1 (- n (length garbage))))
  (define vec (make-vector l #f))
  (define i 0)
  (define (helper i j g)
	(if ( = i l) vec
    	( if ( = j (car g)) ( helper i (+ j 1) (cdr g))
             	(begin (vector-set! vec i ( vector-ref V j))
               	( helper (+ i 1) (+ j 1) g)))))
 (helper 0 0 garbage ))
;;;;;;;;;;;;;;;;;;;;

(define (match a b t)
   
   (define n  (vector-length b))
   (define (helper i)
 	( if ( = i (+ t n))  (void)
      	( begin (vector-set! a  i ( vector-ref b (- i t))) (helper (+ i 1)))))
   (helper t))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;
(define wire%
  	(class object%
    	(init-field a)
    	(init-field b)
    	(init r)
    	(field (resistance r))
    	(init-field potential)
    	(field (current 'u))
    	(field (state 0))
    	(super-new)
 	(define/public (equal) ;;;;;;makes a similar wire
      	(make-object wire% a b resistance potential))
    	(define/public (show-i) current)
    	(define/public (update  k) ;;; used during combine
    	(set! a  (+ k a)) (set! b (+ k b)))
      	(define/public (upgrade1)
  	(if (equal? current 'u) (void)
      	(if (> resistance limit)
          	(set! resistance (/ resistance 2.0))
          	( set! resistance (+ resistance (* k (abs current)))))))

    	(define/public (upgrade2);;;how a wire's resistance changes
      	(if (equal? current 'u) (void)
          	(if ( = state 0)
          	(if (> resistance limit)
              	(begin (set! state 1) (set! resistance (- resistance (* k (abs current)))))
          	( set! resistance (+ resistance (* k (abs current)))))
          	(if ( < resistance optimum)
               	(begin (set! state 0) (set! resistance (+ resistance (* k (abs current)))))
               	(set! resistance (- resistance (* k (abs current))))))))
    	(define/public (upgrade3 f i)
      	( set! resistance (f i)))
    	(define/public (present) ;; for neat representation
      	(list a b resistance potential current state))
    	))
;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define free-wire (make-object wire% 'u 'u 0 0))
  ;;;;;;;;;;;;;;;;;;;;
(define (do-n-give-result f n) ;;; abstraction used during  implementations of Kirchoff rules.
  ( define vec (make-vector n #f))
  ( define (helper i)
 	(if ( = i n)  (vector->list vec)
     	( let((a (f i)))
        	(begin ( vector-set! vec i a)
           	(helper (+ i 1))))))
  (helper 0))
	 
(define (make-table l n) ;; generates table
  (define vec (make-vector n '()))
  (define (helper l)
	(if (null? l) vec
    	(let*((a (car l))
          	(p (- (get-field a a) 1))
          	(q (- (get-field b  a) 1))
          	(m (vector-ref vec p))
          	(n (vector-ref vec q)))
      	(begin (vector-set! vec p  (cons  a m))
             	(vector-set! vec q (cons  a  n))
             	(helper (cdr l))))))
  (helper l))

(define circuit%
  (class object%
	(init-field L) ;; list of all wires
	(init-field n) ; gives number of nodes.
	(field (V (make-table L n) )) ;; table of wires
	(super-new)
	(define/public (equal) ;; though a new circuit is being created not new wires.
  	(define Q (map (lambda(t) (define q (send t equal)) q) L))
  	(define t (make-object circuit% Q   n))
   	t)
	;; there exists an add function
	(define/public (add-wire w1 i j)
  	(define w2 ( send w1 equal))
  	( begin (set-field! a w2 i)
          	(set-field! b w2 j)
          	(if (<= j (vector-length V)) (let (( A (vector-ref V (- i 1)))
               	( B (vector-ref V (- j 1))))
            	(begin ( vector-set! V (- i 1) (cons w2 A))
                   	( vector-set! V (- j 1) (cons w2 B))
                   	(set! L (cons w2 L))))
              	(let ( ( g (make-vector (+ n 1) #f)))
                	(begin (vector-set! g n (list w2)) (match g V 0)
                       	( vector-set! g (- i 1) ( cons w2 (vector-ref g ( - i 1))))
                       	(set! V g) (set! n (+ n 1))
                       	(set! L (cons w2 L)))
  	))))
	;;there exits a delete function.
	(define/public (delete-wire i k j l g)
  	( define garbage (list (+ n 1))) ;;stores values which are to be deleted
  	(begin ( let* ((a (vector-ref V (- i 1)))
        	(b (vector-ref V (- j 1)))
        	( x (remove k a)) ( y (remove l b)))
      	(begin (vector-set! V ( - j 1) y) (vector-set! V ( - i 1) x)
                     	(cond ((null? y) (set! garbage ( cons ( - j 1) garbage)))
            	((null? x) (set! garbage (cons ( - i 1) garbage))))
                              	))
       	(set! n ( - n (length garbage)))
            	(let (( g (generate-simpler V  garbage)))
           	( set! V g)) (set! L (remove g L))))
	;; the biggest function combine combines one object into another
   (define/public (combine r l1 l2)
 	(define C2 ( send r equal))
 	(define m ( get-field n C2))
 	(let*(( t (list-update (get-field L C2) l1 l2 n))
     	(T (append L t)) (vec (make-table T (- (+ n m) 2))))
 	(begin (set! V vec)
        	(set! L T) (set! n (- (+ n m) 2)))))
	(define/public (present)
  	(define (f i)
    	(let((r ( vector-ref V i)))
    	(map ( lambda(t)(send t present)) r)))
  	(do-n-give-result f n))

	(define/public (show-current ini finl res e) ;;for tracing a single wire
  (let((lis (vector-ref V (- ini 1))))
   	(define (helper l)
     	(if (null? l) "wrong input"
         	(let*((x (car l))
            	(p (get-field a x))
            	(q (get-field b x))
            	(r (get-field resistance x))
            	(v (get-field potential x))
            	(i (get-field current x)))
           	(cond ((= p finl) (if (and (= res r) (= e v)) (- i) (helper (cdr l)))) ; needs correction
               	((= q finl) (if (and (= res r) (= e v)) i (helper (cdr l))))
               	(else (helper (cdr l)))))))
                	(helper lis)))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	(define/public (kirchoff-node i) ;;kirchoff rule at one node
  	(define vec1 (let((k (vector-length V)))
  	(make-vector (+ 1 k) 0)))
  	(define (help lis)
  	(if (null? lis) (vector->list vec1)
      	(let* ((w (car lis))
             	(p (get-field a w))
             	(q (get-field b w))
             	(r (get-field resistance w))
             	(e (get-field potential w))
             	(k (if (= p (+ 1 i)) (/ 1 r) (- (/ 1 r))))
             	(x (vector-ref vec1 (- p 1)))
             	(y (vector-ref vec1 (- q 1)))
             	(g (vector-length V))
             	(z (vector-ref vec1 g)))
             	(begin (vector-set! vec1 (- p 1) (+ k x))
                    	(vector-set! vec1 (- q 1) (+ (- k) y))
                    	(vector-set! vec1 g (+ (* e (- k)) z))
                    	(help (cdr lis))))))
(let ((m (vector-ref V i)))
	(help m)))

(define/public (kirchoff-all-nodes)
     	(do-n-give-result (lambda(r)(kirchoff-node r)) n))
	;;;;;;;;;;;;;;;;;;;;;;;;
     	(define/public (volt-list1) ;; used in solve
       	(let* (( a (kirchoff-all-nodes))
     	(b (modified a)))
     	(lin-eqs-sol b)))
	;;;;;;;;;;;;;;;;;;;;;
	(define/public (volt-list2 x y) ;; used in solve2 both uses same each wire-current
  	(let*((a (kirchoff-all-nodes))
        	(b (change a x y)))
        	(lin-eqs-sol b)))
	;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     	(define/public (solve)
     	 
	(final L (lambda (x) (each-wire-current x 1))))  	 
       	;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    
(define/public (solve-two x y)
  (final  L (lambda(t)(each-wire-current t (cons x y)))))
	;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
     	(define/public (each-wire-current one-wire r) ;;used in both solve solve two
      	(let* ((v1 (get-field a one-wire))
   	(v2 (get-field b one-wire))
   	(res (get-field resistance one-wire))
   	(emf (get-field potential one-wire))
    	(z ( if ( eq? r 1) (volt-list1) (volt-list2 (car r) (cdr r))))
   	(volt-vec (list->vector z)))
 	[set-field! current one-wire  (c-from-V v1 v2 emf res volt-vec)]))
	))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (polygonal n r e)
  (define w1 (make-object wire% 1 2 r e))
  	(define S ( make-object circuit% (list w1) 2))
  	(send S add-wire w1 2 3)
  	(  define s ( send S equal))  
  	(send S add-wire w1 1 3)
  	(define i 1)
  	(define (helper x)
    	(if ( = x (- n 1))
        	(begin (send S add-wire (make-object wire% 'u 'u r e)  2 (+ n 1)) S)
        	(begin ( send S combine s (list 1 (+ 2 x)) (list 1 3))
          	(helper (+ x 1)))))
  	(if (= n 1) S
      	(if ( = n 2) (begin ( send S combine s (list 1 3) (list 1 3)) S)
        	(helper 1))))
 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (c-from-V  v1 v2 emf res volt-vec);just calculates current from formula
  (/ [- (- (vector-ref volt-vec (- v1 1))
           (vector-ref volt-vec (- v2 1)) emf)] res))


(define (final sim-list f)
  (begin (map (lambda(x) ( f x)) sim-list) (void)))
 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (create n) ;;creats a list containing n zeros
  (do-n-give-result (lambda(r) 0) n))

(define (condition a)
  (let ((n ( length a)))
    ( cons  1 (create n))))

(define (modified a)
  (let (( c (condition a)))
    (reverse ( cons c (cdr a)))))

;;;;;;;;;;;;; to modify equations;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;create list with all zeroes except one at posn (posn numbering starts from 1)
[define (create-list1 Length posn num)
  (define V1 (make-vector Length 0))
  (vector->list (begin (vector-set! V1 (- posn 1) num) V1))]
[define (create-list2 Length posn1 posn2 num1 num2);creates similar list but with-two posns
  (define V1 (make-vector Length 0))
  (vector->list (begin (vector-set! V1 (- posn1 1) num1)
                       (vector-set! V1 (- posn2 1) num2)V1))]
;takes list1 and replaces xth list with create-list1 x and yth with create-list2
(define (change list1 x y)
  (define V (list->vector list1))
  (let ((aa (length (vector-ref V 01))))
    (begin (vector-set! V (- x 1) (create-list1 aa x 1))
           (vector-set! V (- y 1) (create-list2 aa y aa 1 VOLT));<==this value is voltage;;;;;
           (vector->list V))))
;;;;;;;;;;;;;;;;     	;;;;;;;;;;;;    	;;;;;;;;;;;;

(define (linear-grid n);;;a linear grid type of circuit 
  (define w (make-object wire% 1 2 10 0))
  (define S (make-object circuit% (list w) 2))
  ( send S add-wire w 2 3)
  (send S add-wire w 3 4)
  (define s (send S equal))
  (send S  add-wire w 1 4)
  (define (helper i)
    (if ( = i n) S
        ( begin ( send S combine s (list (+ (* i 2) 1) (+ (* i 2) 2))
                       (list 1 4)) (helper (+ i 1)))))
  (helper 1))


;;;;;;;;;;;;;;;;;;;;;;;;;SHORTEST PATH.;;;;;;;;;;;;;;;;;;;;;;;

(define (max-l lst)
  (if (null? lst) #f
      (foldl (lambda (e r) (if (> e r) e r))
             (car lst)
             (cdr lst))))

(define (satisfying-element cond L) ;; gives out the element in the list which satisfies cond
  (if (null? L) "no element satisfies"
      (if (cond (car L)) (car L)
          (satisfying-element cond (cdr L)))))

(define (shortest-path ini finl S );;gives the nodes of the shortest path
  (define (helper a i b)
    (define (current-getter x)
      (if ( = ( get-field a x) i) (get-field current x)
          (- (get-field current x))))
    (if (= i finl) (hold (reverse a) (reverse b))
        (let*((lis (vector-ref (get-field V S) (- i 1)))
              (c-l (map (lambda(x) (current-getter x)) lis))
              (q (max-l c-l))
              (s1 (satisfying-element (lambda(x) (= (current-getter x) q)) lis))
              (in (get-field a s1))
              (node2 (if (= in i) (get-field b s1) in)))
          (helper (cons node2 a) node2 (cons s1 b)))))
  (helper (list ini) ini '()))

;;;gives effective resistance when obj of circuit and two nodes are given as input
(define (effective-res Obj x y)
  (define (finder lis x);gives current value according to where node x is present in list
    (let ((lv (list->vector lis)))
      (cond [(= (vector-ref lv 0) x) (vector-ref lv 4)]
            [(= (vector-ref lv 1) x) (- (vector-ref lv 4))]
            [#t 0])))
  (define (helper listos x req-val);updates req-val according to lists in listos
    (if (= 0 (length listos)) (/ VOLT (* 1.0 req-val))
        (helper (cdr listos) x (+ req-val (finder (car listos) x)))))
(begin (send Obj solve-two x y)
  (helper (vector-ref (list->vector (send Obj present)) (- x 1)) x 0)))
;=========================================================

;;;;;;;;;;;;;;;;;;;;;MAIN PROGRAM FOR GRAPHS;;;;;;;;;;;;;;;;;;;;
(require racket/gui)
(define frame-size 750)
(define bitmap-size 750)

(define frame (new frame% [label "Single-wire current"]
                   [width frame-size]
                   [height frame-size]))

; Make the drawing area with a paint callback
(define canvas
  (new canvas% [parent frame]
       [paint-callback
        (lambda (canvas dc) (paint dc))]))

; ... pens, brushes, and draw-face are the same as above ...

(define (paint dc) (send dc draw-bitmap face-bitmap 0 0))

; ... pens, brushes, and draw-face are the same as above ...

; Create a bitmap
(define face-bitmap (make-object bitmap% bitmap-size bitmap-size ))
; Create a drawing context for the bitmap
(define bm-dc (make-object bitmap-dc% face-bitmap))
; A bitmap's initial content is undefined; clear it before drawing
(send bm-dc clear)

; Make some pens and brushes
(define black-pen (make-object pen% "BLACK" 1 'solid))
(define yellow-brush (make-object brush% "GREEN" 'solid))
(define red-pen (make-object pen% "BLACK" 2 'solid))

;;Change this to get object sizes to your liking

(define scale-radius 2)
(define (x-point n y)
  (define l '())
  ( define (helper i)
     (if ( =  i n) l
     	(begin (set! l ( cons (list (+ 70 (* i 20)) y) l))
               (helper (+ i 1)))))
  (helper 0))


; Show the frame
(send frame show #f)
;  draw-particles :: [(Radius, Posn)] -> Action
(define (draw l n);main drawing tool for drawing graphs
  (begin
    (send frame show #t)
    (send bm-dc clear)
    (send bm-dc set-brush yellow-brush)
    (send bm-dc set-text-foreground "black")
    (send bm-dc draw-text "x-axis"  (- bitmap-size 50) (- bitmap-size 100))
    (send bm-dc draw-text "y-axis"  50 50)
    (send bm-dc set-pen black-pen)
    (send bm-dc draw-line 50 50 50 (- bitmap-size 50))
    (send bm-dc draw-line 10 (- bitmap-size 100) (- bitmap-size 100) (- bitmap-size 100))
    (send bm-dc set-pen red-pen)
    (map (lambda(p)
           (let*(( x (car p))
                 (y (cadr p)))
             (send bm-dc draw-ellipse x y 2 2)))
         (x-point n (- bitmap-size 100)))
    (map (lambda (p) (let*([posn  p]
                           [diameter 6]
                           [x (+ 50 (* 20 (car posn)))]
                           [y  (- (- bitmap-size 10)   (cadr posn) )])                       
                       (send bm-dc draw-ellipse x y diameter diameter))) l)
    (send canvas refresh)
    (sleep/yield 0.1)))



(define (total-resis S s e);;;gives the total resistance of the wires in the shortest path(sum)
  (let* ((a (shortest-path s e S))(b (hold-r a)))
    (+ 100 (foldr  (lambda( x y) ( + ( get-field resistance x) y)) 0 b ))))

(define (short-path S s e);;gives the the shortest path
  ( hold-l (shortest-path s e S)))

(define (modifier-f f a n)
  ( lambda(x) (+ (f x) (* a (( pow (- n 1)) x)))))



(define (to-lambda l)
  ( define (helper l f r)
 	( if (= r 0) f
      	(helper (cdr l) (modifier-f f (car l) r) (- r  1))))
  (helper  l ( lambda(x) 0) (length l)))


(define (ke i n j)
  (+ 1 ( / (* j (- n 1)) i)))

(define (list-generator i l)
  ( define vec (make-vector i 0))
   (let* (( a ( a-create-linear l))
    	(b (lin-eqs-sol a))
    	(c (to-lambda b))
    	(n (length l)))
   (begin (define (helper j)
        	(if (= i j) (vector->list vec)
            	(begin (vector-set! vec j (list (ke i n j) (c (ke i n j))))
                   	(helper (+ j 1)))))
      	(helper 0))))


;;;;;;;function required for drawing variation of total time for the shortest path
(define (for-min-path n S s e ch-f ch-upgrade  ch-graph )
  (define l '())
  (define (helper i)
	(define upgradew
  (lambda(x j)
	(cond ((eq? j 1)(send x upgrade1))
      	((eq? j 2) (send x upgrade2))
      	(else  ( send x upgrade3 j i)))))
	( if ( = i (+ n 1))
     	(if(equal? ch-f 'short-path) l
        	(let((a (map (lambda(x) (list (car x) (- (cadr x) 100))) l)))
                      	(if (equal? ch-graph 'static)
     	(begin (draw (list-generator 1000 l) n) a)  a)))
     	( begin ( send S solve-two s e)
             	;;;;;;;;;;;;;;;;;;;;
             	(if(eq? ch-f 'short-path) (set! l (cons ( list i (short-path S s e )) l))
                   (set! l (cons (list i (ch-f S s e )) l)) )
        	(if (and (not (equal? (car l) 'f2))
                 	(equal? ch-graph 'motional)) (draw l n) (void))             	;;;;;;;;;;;;;;;;;;;
             	(final (get-field L S) (lambda(x)(upgradew x ch-upgrade)))
             	(helper (+ i 1)))))
  (helper 1))

 

;;;;;;;;;;;;;;;;;;;;;;;;SINGLE WIRE CURRENT

;;function required for drawing variation of current in a wire
(define (for-wire-current  n S w ch-upgrade ch-graph)
(define probe w)
  (define l '())
  (define (helper i)
	(define upgradew
  (lambda(x j)
	(cond ((eq? j 1)(send x upgrade1))
      	((eq? j 2) (send x upgrade2))
      	(else  ( send x upgrade3 j i)))))
    
	(define (f3 S i)
   (begin (define b (send S show-current
                       	(get-field a probe) (get-field b probe)
                       	(get-field resistance probe) (get-field potential probe)))
       	(set-field! current probe b)
       	((lambda(x) (upgradew x ch-upgrade)) probe)
       	b))
 
	( if ( = i (+ n 1))
     	(if ( equal? ch-graph 'static) (begin (draw (list-generator 1000 l) n)
   	(map ( lambda(x)( list (car x) (- (cadr x) 200))) l) )
         	(map ( lambda(x)( list (car x) (- (cadr x) 200))) l))
    	 
     	( begin ( send S solve)            	 
             	(set! l (cons ( list i (+ 200 (f3 S i))) l))
             	(if (equal? ch-graph 'motional) (draw  l n) (void))            	 
             	(final (get-field L S) (lambda(x)(upgradew x ch-upgrade)))
             	(helper (+ i 1)))))
  (helper 1))
;(define a (polygonal 2 10 200))
;(for-wire-current 20 a (make-object wire% 1 2 10 200) 1 'static)  


(defvar fxshift 2)
(defvar wordsize 1)
(defvar fixnumbits (- (* wordsize 8) fxshift))
(defvar *fxlower* (- (expt 2 (- fixnumbits 1))))
(defvar *fxupper* (1- (expt 2 (- fixnumbits 1))))

(defun shl (x width bits)
  "Compute bitwise left shift of x by 'bits' bits, represented on 'width' bits"
  (logand (ash x bits)
          (1- (ash 1 width))))

(defun shr (x width bits)
  "Compute bitwise right shift of x by 'bits' bits, represented on 'width' bits"
  (logand (ash x (- bits))
          (1- (ash 1 width))))

(defun fixnump (x)
	(or (and (integerp x) (<= *fxlower* x *fxupper*))
	    (and (numberp x) (error "Number not supported ~a" x))))

(defun booleanp (x)
	(or (eq 'true x) (eq 'false x)))

(defun charp (x)
	(and (not (numberp x))
        (not (symbolp x))
		(not (listp x)) 
		(standard-char-p x)
		(or (char<= #\Space x #\_))))

(defun nullp (x)
	(eq nil x))

(defun immediatep (x)
	(or (nullp x) (fixnump x) (booleanp x) (charp x)))

(defun unique-label-maker ()
	(let ((count 0))
		(lambda ()
			(let ((L (format nil "L_~d" count)))
				(incf count)
				L))))

(defvar unique-label (unique-label-maker))
(setq unique-label (unique-label-maker))

(defun emit (&rest args)
	(apply 'format (cons t args))
	(fresh-line))

(defvar *bool-t* #b01101111)
(defvar *bool-f* #b00101111)
(defvar *nil* #b00111111)

(defun if-test (expr) (cadr expr))
(defun if-conseq (expr) (caddr expr))
(defun if-altern (expr) (cadddr expr))

(defun ifp (expr)
	(and (eq (car expr) 'if) (eq (length expr) 4)))

(defun emit-if (si env expr)
	(let ((alt-label (funcall unique-label))
		  (end-label (funcall unique-label)))
	(emit-expr si env (if-test expr))
	(emit "    xor ~d" *bool-f*)
	(emit "    jp z, ~a" alt-label)
	(emit-expr si env (if-conseq expr))
	(emit "    jp ~a" end-label)
	(emit "~a:" alt-label)
	(emit-expr si env (if-altern expr))
	(emit "~a: " end-label)))

(defun immediate-rep (x)
	(cond
		((nullp x) #b00111111)
		((fixnump x) (shl x (* 8 wordsize) fxshift))
	    ((booleanp x) (if (eq x 'true) #b01101111 #b00101111))
		((charp x) (char<= #\Space x #\_) (1+ (shl (- (char-code x) (char-code #\Space)) (* wordsize 8) 2)))))

(defun pairp (pair)
	(eq (length pair) 2))

(defun primitivep (x)
	(and (symbolp x) (get x '*is-prim*)))

(defun primitive-emitter (x)
	(or (get x '*emitter*) (error "wrong emitter")))

(defun primcallp (expr)
	(primitivep (car expr)))

(defun variablep (expr)
	(symbolp expr))

(defun letp (expr)
	(and (eq (first expr) 'let)
		(let ((bindings (second expr)))
			(and (> (length bindings) 0)
				(every #'identity (map 'list (lambda (b) (eq (length b) 2)) bindings))))))

(defun emit-primcall (si env expr)
	(let*
		((prim (car expr))
		 (args (cdr expr)))
		;(check-primcall-args prim args)
		(apply (primitive-emitter prim) si env args)))

(defun emit-immediate (x)
	(unless (immediatep x) (error (format t "~a is not a valid immediate" x)))
	(emit "    ld a, ~d" (immediate-rep x)))

(defun emit-stack-save (si)
	(emit "    ld hl, ~d" si) ; HL <- si
	(emit "    add hl, sp")    ; HL <- sp + si
	(emit "    ld [HL], a"))    ; (SP+si) <- A

(defun next-stack-index (si)
	(- si wordsize))

(defun extend-env (var si env)
	(cons (cons var si) env))

(defun emit-stack-load (si)
	(emit "    ld hl, ~d" si) ; HL <- si
	(emit "    add hl, sp")    ; HL <- sp + si
	(emit "    ld a, [HL]"))    ; (SP+si) <- A)

(defun let-bindings (expr)
	(second expr))

(defun let-body (expr)
	(caddr expr))

(defun emit-let (si env expr)
	(defun process-let (bindings si new-env)
		(cond
			((null bindings)
				(emit-expr si new-env (let-body expr)))
			(t 
				(let ((b (first bindings)))
					(emit-expr si env (second b))
					(emit-stack-save si)
					(process-let (rest bindings)
						(next-stack-index si)
						(extend-env (first b) si new-env))))))
	(process-let (let-bindings expr) si env))

(defun emit-variable-ref (env var)
	(cond
		((assoc var env) (emit-stack-load (cdr (assoc var env))))
		(t (error "Unknown variable ~a" var))))

(defun emit-expr (si env expr)
	(cond
		((immediatep expr) (emit-immediate expr))
		((variablep expr) (emit-variable-ref env expr))
		((primcallp expr) (emit-primcall si env expr))
		((letp expr) (emit-let si env expr))
		((ifp expr) (emit-if si env expr))
		(t (emit-app si env expr))
		(t (error "Not a valid expression"))))

(defun emit-function-header (label)
	(emit "~a:" label))

(defun lambda-formals (expr)
	(second expr))

(defun lambda-f (expr)
	(lambda (fmls si env)) (first expr))

(defun process-lambda (fmls si env body)
	(cond
		 ((null fmls) 
		 	(emit-expr si env body)
		 	(emit "    ret"))
		 (t (process-lambda (rest fmls)
		    (- si wordsize)
		    (extend-env (first fmls) si env) body))))

(defun lambda-body (expr)
	(third expr))

(defun emit-lambda (env)
	(lambda (expr label)
		(emit-function-header label)
		(let ((fmls (lambda-formals expr))
			  (body (lambda-body expr)))
		    (process-lambda fmls (- wordsize) env body))))

(defun letrec-bindings (expr)
	(first expr))

(defun unique-labels (vars)
	(loop for var in vars
		collect (funcall unique-label)))

(defun make-initial-env (lvars labels)
	(let ((env nil))
		(loop for lvar in lvars
			  for label in labels
		      collect (extend-env lvar (list label) env))))

(defun emit-interrupt-vectors ()
	(emit "include \"gbhw.inc\"")
	(emit "SECTION \"Vblank\", ROM0[$0040]")
	(emit "    reti")
	(emit "SECTION \"LCDC\", ROM0[$0050]")
	(emit "    reti")
	(emit "SECTION \"Timer\", ROM0[$0058]")
	(emit "    reti")
	(emit "SECTION \"Joypad\", ROM0[$0060]")
	(emit "    reti"))

(defun emit-rom-entry-point ()
	(emit "SECTION \"ROM_entry_point\", ROM0[$0100]")
	(emit "    nop")
	(emit "    jp code_begins"))

(defun emit-rom-header ()
	(emit "SECTION \"rom header\", ROM0[$0104]")
	(emit "    NINTENDO_LOGO")
	(emit "    ROM_HEADER \"0123456789ABCDE\""))

(defun emit-program-entry (expr env)
	(progn
	(emit "code_begins:")
	(emit "    di ; disable interrupts")
	(emit "    ld SP, $FFFE ; set stack to top of RAM")
	(loop for e in expr
		do (emit-expr 0 env e))
	(emit " .loop")
	(emit "    halt")
	(emit "    nop")
	(emit "    jp .loop")))

(defun for-each (func lst)
  (mapc func (first lst) (second lst)))

(defun letrec-body (expr)
	(rest expr))

(defun concat-lists (seq1 seq2)
  (if (null seq1)
      seq2
      (cons (car seq1) (concat-lists (cdr seq1) seq2))))

(defun emit-letrec (expr)
	(let* ((bindings (letrec-bindings expr))
		   (lvars (map 'list #'first bindings))
		   (lambdas (map 'list #'second bindings))
		   (labels (unique-labels lvars))
		   (env (reduce #'concat-lists (make-initial-env lvars labels) :initial-value nil)))
	    (emit-interrupt-vectors)
		(emit-rom-entry-point)
		(emit-rom-header)
		(loop for lbda in lambdas
		      for label in labels
		      do (funcall (emit-lambda env) lbda label))
		(emit-program-entry (letrec-body expr) env)))

(defun call-args (expr)
	(rest expr))

(defun emit-adjust-base (new-sp)
	(emit "    add sp, ~d" new-sp))

(defun emit-call (function)
	(emit "    call ~a" function))

(defun lookup (target env)
	(cadr (assoc target env)))

(defun call-target (expr)
	(first expr))

(defun emit-app (si env expr)
	(defun emit-arguments (si args)
		(unless (null args)
			(emit-expr si env (first args))
			(emit "    ld hl, ~d" si)
			(emit "    add hl, sp")
			(emit "    ld [hl], a")
			(emit-arguments (- si wordsize) (rest args))))
	(emit-arguments (- si (* 2 wordsize)) (call-args expr))
	(emit-adjust-base (+ si wordsize))
	(emit-call (lookup (call-target expr) env))
	(emit-adjust-base (+ (- si) (- wordsize))))

(defmacro define-primitive (prim (si env &rest args) &rest body)
	(declare (ignore si))
	(declare (ignore env))
	`(progn 
		(setf (get ',prim '*is-prim*) t)
		(setf (get ',prim '*prim-name*) "test")
		(setf (get ',prim '*emitter*) 
			(lambda (si env ,@args) (progn ,@body)))))

(defmacro define-raw-primitive (prim (&rest args) &rest body)
	`(progn 
		(setf (get ',prim '*is-prim*) t)
		(setf (get ',prim '*prim-name*) "test")
		(setf (get ',prim '*emitter*) 
			(lambda (,@args) (progn ,@body)))))

(define-primitive fxadd1 (si env arg)
	(emit-expr si env arg)
	(emit "    add a, ~d" (immediate-rep 1)))

(define-primitive fxsub1 (si env arg)
	(emit-expr si env arg)
	(emit "    sub ~d" (immediate-rep 1)))

(define-primitive fixnum->char (si env arg)
	(emit-expr si env arg)
	(emit "    add a, 1"))

(define-primitive char->fixnum (si env arg)
	(emit-expr si env arg)
	(emit "    sub 1"))

(define-primitive null? (si env arg)
	(let ((null-label (funcall unique-label))
		  (end-label (funcall unique-label)))
	(emit-expr si env arg)
	(emit "    sub a, ~d" (immediate-rep nil))
	(emit "    jp z, ~a" null-label)
	(emit "    ld a, ~d" *bool-f*)
	(emit "    jp ~a" end-label)
	(emit "~a:" null-label)
	(emit "    ld a, ~d" *bool-t*)
	(emit "~a:" end-label)))

(define-primitive + (si env arg arg2)
	(emit-expr si env arg)
	(emit "    ld hl, ~d" si) ; HL <- si
	(emit "    add hl, sp")    ; HL <- sp + si
	(emit "    ld [HL], a")    ; (SP+si) <- A
	(emit-expr (- si wordsize) env arg2)
	(emit "    ld b,a")
	(emit "    ld hl, ~d" si) ; HL <- si
	(emit "    add hl, sp")    ; HL <- sp + si
	(emit "    ld a, [HL]")    ; (SP + si) <- A)
	(emit "    add a, b"))

(define-primitive - (si env arg arg2)
	(emit-expr si env arg)
	(emit "    ld hl, ~d" si) ; HL <- si
	(emit "    add hl, sp")    ; HL <- sp + si
	(emit "    ld [HL], a")    ; (SP+si) <- A
	(emit-expr (- si wordsize) env arg2)
	(emit "    ld b,a")
	(emit "    ld hl, ~d" si) ; HL <- si
	(emit "    add hl, sp")    ; HL <- sp + si
	(emit "    ld a, [HL]")    ; (SP + si) <- A)
	(emit "    sub b"))

(define-primitive = (si env arg arg2)
	(let ((eq-label (funcall unique-label))
		  (end-label (funcall unique-label)))
	(emit-expr si env arg)
	(emit "    ld hl, ~d" si) ; HL <- si
	(emit "    add hl, sp")    ; HL <- sp + si
	(emit "    ld [HL], a")    ; (SP+si) <- A
	(emit-expr (- si wordsize) env arg2)
	(emit "    ld b,a")
	(emit "    ld hl, ~d" si) ; HL <- si
	(emit "    add hl, sp")    ; HL <- sp + si
	(emit "    ld a, [HL]")    ; (SP + si) <- A)
	(emit "    sub b")
	(emit "    jp z, ~a" eq-label)
	(emit "    ld a, ~d" *bool-f*)
	(emit "    jp ~a" end-label)
	(emit "~a:" eq-label)
	(emit "    ld a, ~d" *bool-t*)
	(emit "~a:" end-label)))

(define-primitive reset-tilemap (si env)
	(emit "    xor a")
	(emit "    ld hl, rSCY")
	(emit "    ldi [hl], a")
	(emit "    ld [hl], a")
	(emit "    ld [NextCharX], a")
	(emit "    ld [NextCharY], a"))

(define-primitive stop-lcd-wait (si env)
	(emit "stopLCD_wait:")
	(emit "    ld a, [rLY]")
	(emit "    cp 145")
	(emit "    jr nz,stopLCD_wait")
	(emit "    ld hl, rLCDC")
	(emit "    res 7, [hl]"))

(define-primitive load-bitmap-font (si env)
	(emit "    ld de, BitmapFont")
	(emit "    ld hl, _VRAM")
	(emit "    ld bc, BitmapFontEnd - BitmapFont")
    (emit "Copy2BitLoop:")
    (emit "    ld a, [de]")
    (emit "    inc de")
    (emit "    ldi [hl], a")
    (emit "    ldi [hl], a")
    (emit "    dec bc")
    (emit "    ld a,b")
    (emit "    or c")
    (emit "    jr nz, Copy2BitLoop"))

(define-primitive load-palette (si env)
	(emit "    ld a, %00011011")
	(emit "    ld hl, rBGP")
	(emit "    ldi [hl], a")
	(emit "    ldi [hl], a")
	(emit "    cpl")
	(emit "    ldi [hl], a"))
	;(emit "GBPal: dw %0111110000000000")
	;(emit "       dw %0111111111100000")
	;(emit "       dw %0000000000011111")
	;(emit "       dw %0000001111111111")
	;(emit "       dw %1111111111111111"))

(define-primitive turn-on-screen (si env)
	(emit "    ld hl, rLCDC")
	(emit "    set 7, [hl]"))

(define-primitive print-char (si env)
	(emit "NextCharX EQU $C000")
	(emit "NextCharY EQU $C001")
	(emit "PrintChar:")
	(emit "    push hl")
	(emit "    push bc")
	(emit "    push af")
	(emit "    ld a, [NextCharY]")
	(emit "    ld b,a")
	(emit "    ld hl, NextCharX")
	(emit "    ld a, [hl]")
	(emit "    ld c, a")
	(emit "    inc [hl]")
	(emit "    cp 20-1")
	(emit "    call z, NewLine")
	(emit "    xor a")
	(emit "    rr b")
	(emit "    rra")
	(emit "    rr b")
	(emit "    rra")
	(emit "    rr b")
	(emit "    rra")
	(emit "    or c")
	(emit "    ld c,a")
	(emit "    ld hl, _SCRN0")
	(emit "    add hl, bc")
	(emit "    pop af")
	;(emit "    pop af")
	(emit "    push af")
	(emit "    sub 32")
	(emit "    call LCDWait")
	(emit "    ld [hl], a")
	(emit "    pop af")
	(emit "    pop bc")
	(emit "    pop hl")
	(emit "    ret")
	(emit "LCDWait:")
	(emit "    push af")
	(emit "    di")
	(emit "LCDWaitAgain:")
	(emit "    ld a, [rSTAT]")
	(emit "    and %00000010")
	(emit "    jr nz, LCDWaitAgain")
	(emit "    pop af")
	(emit "    ret")
	(emit "NewLine:")
	(emit "    push hl")
	(emit "    ld hl, NextCharY")
	(emit "    inc [hl]")
	(emit "    ld hl, NextCharX")
	(emit "    ld [hl], 0")
	(emit "    pop hl")
	(emit "    ret"))

(define-primitive print-string (si env)
	(emit "PrintString:")
	(emit "    ld a, [hl]")
	(emit "    cp 255")
	(emit "    ret z")
	(emit "    inc hl")
	(emit "    call PrintChar")
	(emit "    jr PrintString")
	(emit "BitmapFont:")
    (emit "    incbin \"Font96.FNT\"")
    (emit "BitmapFontEnd:"))

(define-primitive print-hello-world (si env)
	(emit "    ld hl, Message")
	(emit "    call PrintString")
	(emit " .loop2")
	(emit "    halt")
	(emit "    nop")
	(emit "    jp .loop2")
	(emit "Message: db \"Kitty is a B*tch!\",255"))
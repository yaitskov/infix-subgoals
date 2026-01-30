; defthm subgoals infix formatter and interceptor.
; infix notation is inspired by Haskell
; Copyright (C) 2026 Daniil Iaitskov
;
; Contact:
;
;   dyaitskov@gmail.com
;   https://github.com/yaitskov/infix-subgoals
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
(in-package "ACL2")

(include-book "std/strings/pretty" :dir :system)
(include-book "std/strings/coerce" :dir :system)
(include-book "std/strings/strsubst" :dir :system)
(include-book "std/strings/fast-cat" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "tools/prettygoals/top" :dir :system :TTAGS :all)

(defun sexp-depth (s)
  (declare (xargs :guard t))
  (if (consp s)
      (+ 1
         (max (sexp-depth (car s))
              (sexp-depth (cdr s))))
      0))

(defun wrap-par (v outer-priority inner-priority)
  (declare (xargs :guard (and (stringp v) (natp outer-priority) (natp inner-priority))))
  (if (> outer-priority inner-priority)
      (concatenate 'string "(" v ")")
      v))

(defun mypretty (x)
  (if (stringp x)
      (concatenate 'string "“" (str::strsubst "\"" "”" x) "“")
      (str::pretty x)))

(verify-guards mypretty)

;; (defthm mypretty-string-starts-with-left-double-quote
;;     (implies (stringp s)
;;              (equal "“" (subseq (mypretty s) 0 3)))
;;   :rule-classes nil)

;; (defun foo (x)
;;   (if (stringp x)
;;       (str::fast-string-append x "+")
;;       x))

;; (defthm append
;;     (implies (and (stringp a) (stringp b))
;;              (equal (
;; need a lemma for:
;; (IMPLIES (STRINGP S)
;;          (EQUAL "+"
;;                 (IMPLODE (LIST (CAR (NTHCDR (LEN (EXPLODE S))
;;                                             (APPEND (EXPLODE S) '(#\+))))))))

;; (defthm foo-ends-with-pluss
;;     (implies (stringp s)
;;              (equal "+" (subseq (foo s)
;;                                 (- (length (foo s)) 1)
;;                                 (length (foo s)))))
;;   :rule-classes nil
;;   )


;; (defthm mypretty-string-ends-with-right-double-quote
;;     (implies (stringp s)
;;              (equal "“" (subseq (mypretty s)
;;                                 (- (length (mypretty s)) 3)
;;                                 (length (mypretty s)))))
;;   ; :rule-classes nil
;;   )

(defun me (x y)
  (nat-list-measure (list (sexp-depth x) (len x) y)))

(mutual-recursion
 (defun infixargs (op args op-priority)
   (declare (xargs
             :guard (and (stringp op) (natp op-priority))
             :verify-guards nil
             :measure (me args 0)))
   (if (consp args)
       (if (consp (cdr args))
           (concatenate 'string
                        (infix2 (car args) op-priority)
                        op
                        (infixargs op (cdr args) op-priority))
           (infix2 (car args) op-priority))
       ""))

 (defun infixargs-wrap (sexp outer-priority op inner-priority)
   (declare (xargs
             :guard (and (stringp op) (natp outer-priority) (natp inner-priority))
             :verify-guards nil
             :measure (me sexp 7)))
   (wrap-par (infixargs op sexp inner-priority)
             outer-priority
             inner-priority))

 (defun infixfuncall (fargs)
   (declare (xargs
             ;; :guard (and (stringp op) (natp outer-priority) (natp inner-priority))
             ;; :verify-guards nil
             :measure (me fargs 8)))
   (if (consp fargs)
       (concatenate 'string
                    " "
                    (infix2 (car fargs) 100)
                    (infixfuncall (cdr fargs)))
       ""))

 (defun infix2 (sexp outer-priority)
   (declare (xargs
             :guard (natp outer-priority)
             :verify-guards nil
             :measure (me sexp 9)))
   (case-match sexp
       (('iff . a) (infixargs-wrap a outer-priority " ⟺ " 10))
     (('implies . a) (infixargs-wrap a outer-priority " ⟹ " 20))
     (('or . a) (infixargs-wrap a outer-priority " ∨ " 30))
     (('and . a) (infixargs-wrap a outer-priority " ∧ " 40))
     (('xor . a) (infixargs-wrap a outer-priority " ⊕ " 45))
     (('equal . a) (infixargs-wrap a outer-priority " = " 50))
     (('< . a) (infixargs-wrap a outer-priority " < " 51))
     (('> . a) (infixargs-wrap a outer-priority " > " 51))
     (('<= . a) (infixargs-wrap a outer-priority " ≤ " 51))
     (('>= . a) (infixargs-wrap a outer-priority " ≥ " 51))
     (('app . a) (infixargs-wrap a outer-priority " ◇ " 52))
     (('list . a)
      (concatenate 'string
                   "[ "
                   (infixargs-wrap a 0 ", " 52)
                   " ]"))
     (('cons a b)
      (wrap-par (concatenate 'string
                             (infix2 a 55)
                             ":"
                             (infix2 b 55))
                outer-priority
                55))
     (('+ . a) (infixargs-wrap a outer-priority " + " 61))
     (('- . a) (infixargs-wrap a outer-priority " - " 61))
     (('* . a) (infixargs-wrap a outer-priority " * " 71))
     (('/ . a) (infixargs-wrap a outer-priority " ÷ " 71))
     (('consp a)
      (wrap-par
       (concatenate 'string
                    (infix2 a 83)
                    " :: _:_")
       outer-priority
       83))
     (('true-listp a)
      (wrap-par
       (concatenate 'string
                    (infix2 a 84)
                    " :: [_]")
       outer-priority
       84))
     (('nth i l)
      (wrap-par
       (concatenate 'string
                    (infix2 l 85)
                    " !! "
                    (infix2 i 0))
       outer-priority
       85))
     (('not a)
      (wrap-par
       (concatenate 'string "¬" (infix2 a 90))
       outer-priority
       90))
     (t "t")
     (nil "nil")
     (& (if (and (consp sexp) (symbolp (car sexp)))
            (wrap-par
             (concatenate 'string
                         (str::pretty (car sexp))
                         (infixfuncall (cdr sexp)))
             outer-priority
             99)
            (mypretty sexp))))))

(verify-guards infix2)

(defun infix (sexp) (infix2 sexp 0))

(verify-guards infix)

(thm (stringp (infix
              '(IMPLIES
                (AND (CONSP L)
                 (< 0 (+ 1 (LEN (CDR L))))
                 (<= 0 X)
                 (< X (+ 1 (LEN (CDR L))))
                 (NOT (ZP X))
                 (EQUAL (NTH (+ -1 X) (CDR L)) " "))
                (EQUAL (CAR L) " ")))))


; (thm (equal "“abc”" (infix "abc")))

(defattach acl2::post-untranslate-hook infix)

(ns clj-lisp.core
  (:refer-clojure :exclude [apply eval find-var next read rest val])
  (:require [clojure.string :as str]))

(def ^:const k-lpar \()
(def ^:const k-rpar \))
(def ^:const k-quote \')
(def k-nil {:tag :nil :data :nil})

(defn safe-car [obj]
  (if (= :cons (:tag obj)) @(:car obj) k-nil))

(defn safe-cdr [obj]
  (if (= :cons (:tag obj)) @(:cdr obj) k-nil))

(defn make-error [s]
  {:tag :error :data s})

(def sym-table (atom [["nil" k-nil]]))

(defn lookup-sym [s tbl]
  (when-not (empty? tbl)
    (let [[[k v] & rest] tbl]
      (if (= k s)
        v
        (recur s rest)))))

(defn make-sym [s]
  (if-let [sym (lookup-sym s @sym-table)]
    sym
    (let [ret {:tag :sym :data s}]
      (reset! sym-table (cons [s ret] @sym-table))
      ret)))

(def sym-t (make-sym "t"))
(def sym-quote (make-sym "quote"))
(def sym-if (make-sym "if"))
(def sym-lambda (make-sym "lambda"))
(def sym-defun (make-sym "defun"))
(def sym-setq (make-sym "setq"))
(def sym-loop (make-sym "loop"))
(def sym-return (make-sym "return"))
(def loop-val (atom k-nil))

(defn make-num [n]
  {:tag :num :data n})

(defn make-cons [a d]
  {:tag :cons :car (atom a) :cdr (atom d)})

(defn make-subr [f]
  {:tag :subr :data f})

(defn make-expr [args env]
  {:tag :expr :args (safe-car args) :body (safe-cdr args) :env env})

(defn nreconc [lst tail]
  (if-not (= :cons (:tag lst))
    tail
    (let [tmp @(:cdr lst)]
      (reset! (:cdr lst) tail)
      (recur tmp lst))))

(defn nreverse [lst]
  (nreconc lst k-nil))

(defn pairlis [lst1 lst2]
  (loop [lst1 lst1 lst2 lst2 acc k-nil]
    (if-not (and (= :cons (:tag lst1)) (= :cons (:tag lst2)))
      (nreverse acc)
      (recur @(:cdr lst1)
             @(:cdr lst2)
             (make-cons (make-cons @(:car lst1) @(:car lst2)) acc)))))

(defn delimiter? [c]
  (contains? #{k-lpar k-rpar k-quote \tab \newline \space \return} c))

(defn skip-spaces [s]
  (str/triml s))

(defn make-num-or-sym [s]
  (try (make-num (Integer/parseInt s))
       (catch NumberFormatException _
         (make-sym s))))

(defn position [f s]
  (let [i (reduce (fn [i c] (if (f c) (reduced i) (inc (long i)))) 0 s)]
    (when-not (= i (count s))
      i)))

(defn read-atom [s]
  (if-let [i (position delimiter? s)]
    [(make-num-or-sym (subs s 0 i)) (subs s i)]
    [(make-num-or-sym s) ""]))

(defn look-ahead [s]
  (let [t (skip-spaces s)
        c (if (empty? t) \_ (first s))
        rest (if (empty? t) "" (subs t 1))]
    [t c rest]))

(defn read [s]
  (letfn [(read-quote [s]
            (let [[elm next] (read s)]
              [(make-cons (make-sym "quote") (make-cons elm k-nil)) next]))
          (read-list [s acc]
            (let [[s c rest] (look-ahead s)]
              (if (empty? s)
                [(make-error "unfinished parenthesis") ""]
                (if (= c k-rpar)
                  [(nreverse acc) rest]
                  (let [[elm next] (read s)]
                    (if (= :error (:tag elm))
                      [elm next]
                      (read-list next (make-cons elm acc))))))))]
    (let [[s c rest] (look-ahead s)]
      (if (empty? s)
        [(make-error "empty input") ""]
        (condp = c
          k-rpar [(make-error (str "invalid syntax: " s)) ""]
          k-lpar (read-list rest k-nil)
          k-quote (read-quote rest)
          (read-atom s))))))

(defn print-obj [obj]
  (letfn [(print-list [obj delimiter acc]
            (if (= :cons (:tag obj))
              (print-list @(:cdr obj)
                          " "
                          (str acc delimiter (print-obj @(:car obj))))
              (if (= :nil (:tag obj))
                acc
                (str acc " . " (print-obj obj)))))]
    (case (:tag obj)
      (:num :sym :nil) (:data obj)
      :error (str "<error: " (:data obj) ">")
      :cons (str \( (print-list obj "" "") \))
      :subr "<subr>"
      :expr "<expr>")))

(defn find-var-in-frame [s alist]
  (let [x (safe-car (safe-car alist))]
    (if (= :sym (:tag x))
      (if (= s (:data x))
        (safe-car alist)
        (recur s (safe-cdr alist)))
      k-nil)))

(defn find-var [sym env]
  (if (= :cons (:tag env))
    (let [pair (find-var-in-frame (:data sym) @(:car env))]
      (if (= :nil (:tag pair))
        (recur sym @(:cdr env))
        pair))
    k-nil))

(def g-env (make-cons k-nil k-nil))

(defn add-to-env! [sym val env]
  (when (= :cons (:tag env))
    (let [car (:car env)]
      (reset! car (make-cons (make-cons sym val) @car)))))

(defn update-var! [sym val env]
  (let [bind (find-var sym env)]
    (if (= :cons (:tag bind))
      (reset! (:cdr bind) val)
      (add-to-env! sym val g-env))))

(defn eval [obj env]
  (letfn [(eval-cons [obj env]
            (let [opr (safe-car obj)
                  args (safe-cdr obj)]
              (condp = opr
                sym-quote (safe-car args)
                sym-if (if (= k-nil (eval (safe-car args) env))
                         (eval (safe-car (safe-cdr (safe-cdr args))) env)
                         (eval (safe-car (safe-cdr args)) env))
                sym-lambda (make-expr args env)
                sym-defun (let [sym (safe-car args)
                                expr (make-expr (safe-cdr args) env)]
                            (add-to-env! sym expr g-env)
                            sym)
                sym-setq (let [sym (safe-car args)
                               val (eval (safe-car (safe-cdr args)) env)]
                           (update-var! sym val env)
                           val)
                sym-loop (loop' args env)
                sym-return (let [val (eval (safe-car args) env)]
                             (reset! loop-val val)
                             (make-error ""))
                (apply (eval opr env) (evlis args env k-nil)))))
          (evlis [lst env acc]
            (if (= :nil (:tag lst))
              (nreverse acc)
              (let [elm (eval (safe-car lst) env)]
                (if (= :error (:tag elm))
                  elm
                  (evlis (safe-cdr lst) env (make-cons elm acc))))))
          (progn [body env acc]
            (if (= :cons (:tag body))
              (let [ret (eval @(:car body) env)]
                (if (= :error (:tag ret))
                  ret
                  (progn @(:cdr body) env ret)))
              acc))
          (loop' [body env]
            (let [ret (progn body env k-nil)]
              (if (= :error (:tag ret))
                (if (empty? (:data ret)) @loop-val ret)
                (loop' body env))))
          (apply [f args]
            (if (= :error (:tag f))
              f
              (if (= :error (:tag args))
                args
                (if (= :subr (:tag f))
                  ((:data f) args)
                  (if (= :expr (:tag f))
                    (progn (:body f) (make-cons (pairlis (:args f) args) (:env f)) k-nil)
                    (make-error (str (print-obj f) " is not function")))))))]
    (if (= :sym (:tag obj))
      (if-let [pair (find-var obj env)]
        (safe-cdr pair)
        (make-error (str (:data obj) " has no value")))
      (if (= :cons (:tag obj))
        (eval-cons obj env)
        obj))))

(defn subr-car [args]
  (safe-car (safe-car args)))

(defn subr-cdr [args]
  (safe-cdr (safe-car args)))

(defn subr-cons [args]
  (make-cons (safe-car args) (safe-car (safe-cdr args))))

(defn subr-eq [args]
  (let [x (safe-car args)
        y (safe-car (safe-cdr args))]
    (if (and (= :num (:tag x)) (= :num (:tag y)))
      (if (= (:data x) (:data y)) sym-t k-nil)
      (if (identical? x y) sym-t k-nil))))

(defn subr-atom [args]
  (if (= :cons (:tag (safe-car args))) k-nil sym-t))

(defn subr-numberp [args]
  (if (= :num (:tag (safe-car args))) sym-t k-nil))

(defn subr-symbolp [args]
  (if (= :sym (:tag (safe-car args))) sym-t k-nil))

(defn subr-add-or-mul [f init-val]
  (let [doit (fn [args acc]
               (if-not (= :cons (:tag args))
                 (make-num acc)
                 (if-not (= :num (:tag @(:car args)))
                   (make-error "wrong type")
                   (recur @(:cdr args) (f acc (:data @(:car args)))))))]
    (fn [args]
      (doit args init-val))))

(def subr-add (subr-add-or-mul (fn [x y] (+ (long x) (long y))) 0))
(def subr-mul (subr-add-or-mul (fn [x y] (* (long x) (long y))) 1))

(defn subr-sub-or-div-or-mod [f]
  (fn [args]
    (let [x (safe-car args)
          y (safe-car (safe-cdr args))]
      (if (and (= :num (:tag x)) (= :num (:tag y)))
        (make-num (f (:data x) (:data y)))
        (make-error "wrong type")))))

(def subr-sub (subr-sub-or-div-or-mod (fn [x y] (- (long x) (long y)))))
(def subr-div (subr-sub-or-div-or-mod (fn [x y] (quot (long x) (long y)))))
(def subr-mod (subr-sub-or-div-or-mod (fn [x y] (mod (long x) (long y)))))

(defn repl []
  (print "> ")
  (flush)
  (when-let [l (read-line)]
    (let [obj (eval (first (read l)) g-env)]
      (println (print-obj obj))
      (recur))))

(add-to-env! (make-sym "car") (make-subr subr-car) g-env)
(add-to-env! (make-sym "cdr") (make-subr subr-cdr) g-env)
(add-to-env! (make-sym "cons") (make-subr subr-cons) g-env)
(add-to-env! (make-sym "eq") (make-subr subr-eq) g-env)
(add-to-env! (make-sym "atom") (make-subr subr-atom) g-env)
(add-to-env! (make-sym "numberp") (make-subr subr-numberp) g-env)
(add-to-env! (make-sym "symbolp") (make-subr subr-symbolp) g-env)
(add-to-env! (make-sym "+") (make-subr subr-add) g-env)
(add-to-env! (make-sym "*") (make-subr subr-mul) g-env)
(add-to-env! (make-sym "-") (make-subr subr-sub) g-env)
(add-to-env! (make-sym "/") (make-subr subr-div) g-env)
(add-to-env! (make-sym "mod") (make-subr subr-mod) g-env)
(add-to-env! sym-t sym-t g-env)
(repl)

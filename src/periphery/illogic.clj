(ns periphery.illogic)

(deftype LogicVar [n]
  clojure.lang.Named
  (getName [_] (str n)))

(defmethod print-method LogicVar
  [lvar ^java.io.Writer w]
  (.write w (str (name lvar))))

(defn lvar
  [name]
  (LogicVar. (symbol (str "_." name))))

(defn lvar?
  [lvar]
  (instance? LogicVar lvar))

(def empty-s {})

(defn ext-s-no-check
  [lvar val s]
  (assoc s lvar val))

(defn walk
  [v s]
  (if (lvar? v)
    (if-let [a (get s v)]
      (walk a s)
      v)
    v))

(defn non-empty-seq?
  [s]
  (and (sequential? s) (seq s)))

(defn occurs-check
  "Does x occur nested in or at v in s."
  [x v s]
  (let [v (walk v s)]
    (cond
      (lvar? v) (= x v)
      (non-empty-seq? v) (or (occurs-check x (first v) s)
                             (occurs-check x (rest v) s)))))

(defn ext-s
  [lvar val s]
  (when-not (occurs-check lvar val s)
    (ext-s-no-check lvar val s)))

(defn unify
  [left right s]
  (let [left (walk left s)
        right (walk right s)]
    (cond
      (= left right) s

      (lvar? left) (if (lvar? right)
                     (ext-s-no-check left right s)
                     (ext-s left right s))

      (lvar? right) (ext-s right left s)

      (and (non-empty-seq? left) (non-empty-seq? right))
      (let [s (unify (first left) (first right) s)]
        (and s (unify (rest left) (rest right) s))))))

(defn walk*
  [val s]
  (let [val (walk val s)]
    (cond
      (lvar? val) val ;; redundant, but leaving it for now
      (non-empty-seq? val) (cons (walk* (first val) s)
                                 (walk* (rest val) s))
      :else val)))

(defn reify-name
  [n]
  (symbol (str "_." n)))

(defn reify-s
  [val s]
  (let [val (walk val s)]
    (cond
      (lvar? val) (ext-s val (reify-name (count s)) s)
      (non-empty-seq? val) (reify-s (rest val) (reify-s (first val) s))
      :else s)))

(defn reify
  [val s]
  (let [val (walk val s)]
    (walk* val (reify-s val empty-s))))

;;; Streams

(defmacro mzero [] nil)

(defmacro unit [a] a)

(defmacro choice [a f] [a f])

(defmacro -inc [e] `(fn [] ~e))

(defmacro case-inf
  [e & rest]
  (let [[a b c d] (partition 2 rest)
        [_ e0]     a
        [[f'] e1]  b
        [[a'] e2]  c
        [[a f] e3] d]
    `(let [a-inf# ~e]
       (cond
         (not a-inf#) ~e0

         (fn? a-inf#) (let [~f' a-inf#] ~e1)

         (and (non-empty-seq? a-inf#) (fn? (second a-inf#)))
         (let [[~a ~f] a-inf#] ~e3)

         :else (let [~a' a-inf#] ~e2)))))

(defn mplus
  [a-inf f]
  (case-inf a-inf
    _      (f)
    [f']   (-inc (mplus (f) f'))
    [a]    (choice a f)
    [a f'] (choice a #(mplus (f) f'))))

(defmacro mplus*
  [e & es]
  (if (seq es)
    `(mplus ~e (fn [] (mplus* ~@es)))
    e))

(defn bind
  [a-inf g]
  (case-inf a-inf
    _     (mzero)
    [f]   (-inc (bind (f) g))
    [a]   (g a)
    [a f] (mplus (g a) #(bind (f) g))))

(defmacro bind*
  [e & gs]
  (if (seq gs)
    (let [[g & gs] gs]
      `(bind* (bind ~e ~g) ~@gs))
    e))

(defmacro fresh
  [xs g & gs]
  `(fn [s#]
     (-inc
      (let ~(vec (mapcat (juxt identity lvar) xs))
        (bind* (~g s#) ~@gs)))))

(defn -take
  [n f]
  (when-not (and n (zero? n))
    (case-inf (f)
      _     ()
      [f]   (-take n f)
      [a]   a
      [a f] (cons (first a) (-take (and n (- n 1)) f)))))

(defmacro run
  [n [x] & gs]
  `(-take ~n
     (fn []
       ((fresh [~x] ~@gs
               (fn [s#]
                 (cons (reify ~x s#) '())))
        empty-s))))

(defmacro run*
  [x & gs]
  `(run false ~x ~@gs))

(defmacro ==
  [left right]
  `(fn [s#]
     (if-let [res# (unify ~left ~right s#)]
       (unit res#)
       (mzero))))

(defmacro conde
  [& gs]
  (let [s (gensym "s_")
        make-bind* (fn [[g & gs]]
                     `(bind* (~g ~s) ~@gs))]
    `(fn [~s]
       (-inc
        (mplus* ~@(map make-bind* gs))))))

(defmacro project
  "Projects the current value of bindings onto logic variables. Kinda
  sucks, though."
  [xs & gs]
  (let [s (gensym "s_")]
    `(fn [~s]
       (let ~(vec (mapcat (juxt identity (fn [g] `(walk ~g ~s))) xs))
         ((fresh [] ~@gs) ~s)))))



(comment
  (lvar 'foo) ;;=> _.foo

  (lvar? (lvar 'foo)) ;;=> true
  (lvar? '_.foo)      ;;=> false

  (= (lvar 'foo) (lvar 'foo)) ;;=> false

  (ext-s-no-check (lvar 'foo) 1 empty-s) ;;=> {_.foo 1}

  (walk :foo empty-s) ;;=> :foo
  (let [foo (lvar 'foo)]
    (walk foo {foo 1}))
  ;;=> 1

  (let [q (lvar 'q)
        a (lvar 'a)
        b (lvar 'b)]
    (occurs-check q a {a q}))
  ;;=> true

  (let [q (lvar 'q)
        a (lvar 'a)
        b (lvar 'b)]
    (occurs-check q a {a [1 2 3 q]}))
  ;;=> true

  (let [q (lvar 'q)
        a (lvar 'a)
        b (lvar 'b)]
    (occurs-check q a {b q}))
  ;;=> false

  (ext-s (lvar 'q) 1 empty-s) ;;=> {_.q 1}

  (let [q (lvar 'q)
        a (lvar 'a)]
    (ext-s q a {a q})) ;;=> nil

  (unify (lvar 'q) 1 empty-s) ;;=> {_.q 1}
  (unify 1 1 empty-s) ;;=> {}
  (let [q (lvar 'q)]
    (unify [1 q 3] [1 2 3] empty-s))
  ;;=> {_.q 2}

  (let [x (lvar 'x)
        y (lvar 'y)
        z [x y]
        s (unify y 2 (unify x 1 empty-s))]
    (walk* z s))
  ;;=> (1 2)

  (let [x (lvar 'x)
        y (lvar 'y)
        z [x y]
        s (unify x :foo empty-s)]
    (reify-s z s))
  ;;=> {_.y _.1, _.x :foo}

  (mzero) ;;=> nil
  (unit 1) ;;=> 1
  (unit [1 2 3]) ;;=> [1 2 3]
  (let [a :a]
    (unit a)) ;;=> :a
  (choice :a #()) ;;=> [:a #()]
  (-inc (+ 1 2)) ;;=> fn

  (defn nevero
    []
    (fn [] (nevero)))

  (run 2 [q]
    (conde
      [(fresh [x]
         (== x :foo)
         (== q x))]
      [(== q 1)]
      [(nevero)]))

  (run* [q]
    (== [1 q 3] [1 2 3]))

  (run 1 [q]
       (fresh [x y z]
              (== q [x y z])))
  (run* [q]
        (fresh [x y]
               (== x 1)
               (== y 2)
               (project [x y]
                        (== q (+ x y)))))
  )


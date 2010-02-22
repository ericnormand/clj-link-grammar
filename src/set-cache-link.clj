(ns link-grammar)

; Each word takes a number of grammatical roles in a sentence.
; Those roles are represented by links.
; The sum of all roles in a sentence is a link disjunct.
; Each link disjunct has a list of left link possibilities and a list of right link possibilities.
; A link possibility represents the type of link a word can make.
; A link possibility to the left means
; that the word will link with another word to its left that has the same link possibility to its
; right.

; A link disjunct looks like this: {:left [:a :b :c] :right '(:z :y :x)}.
; Each keyword in the :left vec is a left link possibility.  Likewise for the :right vec.
; The order of the links is significant.
; Each seq is in the order of farthest first.
; Left links closer to the beginning of the list link with words closer to the beginning of the 
; sentence.
; Right links closer to the beginning of the list link with words closer to the end of the sentence.

; A link disjunct is valid if all link possibilities are linked.

; A link grammar parser tries to find a mapping of words to disjuncts where every disjunct is valid
; and no links cross each other.
; Links cross when arcs drawn between linked words cross.
; Imagine a sentence "The brown dog runs."
; Imagine a linking where "the" is linked with "dog" and "brown" is linked with "runs".
; Those two links cross.

; Additionally, the graph of links has to be fully connected.

; Because of the large number of ways words can link, we define a regular language for generating
; link disjuncts.

; Start -> Statement
; Statement -> link | all | any | opt | not | 0om | 1om
; link -> rightlink | leftlink
; rightlink -> [:right linkname]
; leftlink -> [:left linkname]
; all -> [:all Statement*]
; any -> [:any Statement*]
; opt -> [:opt Statement*]
; not -> [:not Statement]
; 0om -> [:0om Statement]
; 1om -> [:1om Statement]

; predeclare the functions
(declare parse-all)
(declare parse-right)
(declare parse-left)
(declare parse-opt)
(declare parse-any)
(declare parse-0om)
(declare parse-1om)

; this needs to be safe even when working on infinite lazy seqs
(defn right-size?
  "Does this disjunct pass the test of length?  That is, does it require too many links to the left or right than exist in the sentence?"
  [l r disj]
  (and (nil? (seq (drop l (:left disj))))
       (nil? (seq (drop r (:right disj))))))

; Parse any Statement.
(defn parse-statement
  "return a list of disjuncts (mutually exclusive left/right lists) for a given distance l from the left and r from the right"
  [l r disjuncts statement]
  (filter #(right-size? l r %)
   (let [tp (first statement)]
     (cond
       (= :right tp)
       (parse-right l r disjuncts (second statement))
       (= :left tp)
       (parse-left l r disjuncts (second statement))
       (= :all tp)
       (parse-all l r disjuncts (rest statement))
       (= :any tp)
       (parse-any l r disjuncts (rest statement))
       (= :opt tp)
       (parse-opt l r disjuncts (second statement))
       (= :0om tp)
       (parse-0om l r disjuncts (second statement))
       (= :1om tp)
       (parse-1om l r disjuncts (second statement))))))


; we use a [] for left links because we want conjoining to the end.
; we use a () for right links because we want conjoining to the beginning.
(defn get-disjuncts [l r statement]
  (parse-statement l r [{:left [] :right nil}] statement))

(defn parse-right [l r disjuncts link]
  (map #(assoc % :right (conj (:right %) link)) disjuncts))

(defn parse-left [l r disjuncts link]
  (map #(assoc % :left (conj (:left %) link)) disjuncts))

(defn parse-all [l r disjuncts alls]
  (if (seq alls)
    (parse-all l r (parse-statement l r disjuncts (first alls)) (rest alls))
    disjuncts))

(defn parse-any [l r disjuncts anys]
  (mapcat #(parse-statement l r disjuncts %) anys))

; Add a new disjunct which contains the optional statement.  Keep the old disjunct, too.
(defn parse-opt [l r disjuncts opt]
  (lazy-cat disjuncts (parse-statement l r disjuncts opt)))

(defn parse-0om [l r disjuncts thing]
  (parse-opt l r disjuncts [:1om thing]))

(defn parse-1om [l r disjuncts thing]
  (let [d (parse-statement l r disjuncts thing)]
    (if (seq d)
      (lazy-cat d (parse-1om l r d thing)))))


; is this used? ; no
(defn flatten [x] 
  (let [s? #(instance? clojure.lang.Sequential %)] 
    (filter (complement s?) (tree-seq s? seq x))))



(defn matches? [L R]
  (and (seq L)
       (seq R)
       (= (first L) (first R))))



(declare sb)

; functions for matching



(defn cross-cat 
  "concat the cross product of two list"
  [as bs]
  (when (and (seq as) (seq bs))
    (set (for [a as b bs]
	   (clojure.set/union a b)))))


(defn add-to-all
  [coll v]
  (reduce #(conj %1 (conj %2 v))
	  #{}
	  coll))

(defn inc-all
  [sols n]
  (set
   (for [sol sols]
     (set (for [link sol]
	    (assoc link 
	      :a (+ n (:a link))
	      :b (+ n (:b link))))))))

; what is L & R?
(defn process-adjacents 
  [L R]
  ;(prn :process-adjacents L R)
  (cond
    ;; if both are nil, we have an empty match (no links are generated)
    (and (nil? (seq L))
	 (nil? (seq R)))
    #{#{}}
        
    ;; otherwise, we have no match
    :otherwise
    #{}))


(defn process-matches-when-match-left
  [a b L sl R]
  (when (matches? L R)
    (add-to-all 
     (sb (rest L) sl (rest R))
     {:a a :b b :type (first L)})))

(defn process-matches-when-match-right
  [a b L sl R n]
  (when (matches? L R)
    (inc-all
     (add-to-all 
      (sb (rest L) sl (rest R))
      {:a a :b b :type (first L)})
     n)))


(defn process-matches-when-no-match-left
  [L sr R]
  (sb L sr R))

(defn process-matches-when-no-match-right
  [L sr R n]
  (inc-all
   (sb L sr R)
   n))



(defn process-sub-matches
  [L sen R i d]
  (let [sl (subvec sen 0 i)
	sr (subvec sen (inc i))
	;; sub solutions when a left link matches a word
	;; when left match is successful, add a link to all
	;; recursive matches on the left side
	lwm (process-matches-when-match-left 0 (inc (count sl)) L sl (:left d))

	;; sub solutions when the right link matches a word
	;; when right match is successful, add a link to all 
	;; recursive matches on the right side (after incrementing them by i+1)
	wrm (process-matches-when-match-right 0 (inc (count sr)) (:right d) sr R (inc (count sl)))

	;; we can count the cross-product of left and right solutions as global solutions
	mm (cross-cat lwm wrm)

	;; sub solutions where right does not match
	wrme (when (seq lwm) 
	       (process-matches-when-no-match-right (:right d) sr R (inc (count sl))))
	
	lm (cross-cat lwm wrme)

	;; sub solutions where left does not match
	;; should only be done when L is nil, to avoid repeated recursion
	lwme (when (and (seq wrm) (nil? (seq L)))
	       (process-matches-when-no-match-left L sl (:left d)))
	
	;; order is important because wrm might be nil
	rm (cross-cat wrm lwme)]
    (clojure.set/union mm lm rm)))






(defn process-non-prime 
  [L sen R i]
  (apply clojure.set/union
	 (for [i (range (count sen)) 
	       :when (not (or (> (count L) (inc i))
			      (> (count R) (- (count sen) i)) ))
	       :let [disjs (nth sen i)
		     right-size (for [d disjs 
				      :when (right-size? (inc i) (- (count sen) i) d)] d)
		     lefts (set (map :left right-size))
		     rights (set (map :right right-size))
		     sl (subvec sen 0 i)
		     sr (subvec sen (inc i))
		     ls (reduce #(assoc %1 %2 (process-matches-when-match-left 0 (inc (count sl)) L sl %2))
				{}
				lefts)
		     rs (reduce #(assoc %1 %2 (process-matches-when-match-right 0 (inc (count sr)) %2 sr R (inc (count sl))))
				{}
				rights)]
	       d right-size]
	   (let [
		 ;; sub solutions when a left link matches a word
		 ;; when left match is successful, add a link to all
		 ;; recursive matches on the left side
		 lwm (ls  (:left d))

		 ;; sub solutions when the right link matches a word
		 ;; when right match is successful, add a link to all 
		 ;; recursive matches on the right side (after incrementing them by i+1)
		 wrm (rs (:right d))

		 ;; we can count the cross-product of left and right solutions as global solutions
		 mm (cross-cat lwm wrm)

		 ;; sub solutions where right does not match
		 wrme (when (seq lwm) 
			(process-matches-when-no-match-right (:right d) sr R (inc (count sl))))
	
		 lm (cross-cat lwm wrme)

		 ;; sub solutions where left does not match
		 ;; should only be done when L is nil, to avoid repeated recursion
		 lwme (when (and (seq wrm) (nil? (seq L)))
			(process-matches-when-no-match-left L sl (:left d)))
	
		 ;; order is important because wrm might be nil
		 rm (cross-cat wrm lwme)]
	     (clojure.set/union mm lm rm)))))


; L is the seq of right links from the left word
; R is the seq of left links from the right word
; sen is the seq of words between them
(defn sb [L sen R]
  (cond
    ;; if sen is empty, they are adjacent
    (nil? (seq sen))
    (process-adjacents L R)
    
    ;; if L or R is bigger than sen, impossible to connect
    (or (> (count L) (count sen))
	(> (count R) (count sen)))
    #{}

    ;; otherwise, non-adjacent
    :otherwise
    (process-non-prime L sen R 0)))




(defn process-djs [sen]
  (apply clojure.set/union
	 (let [ss (subvec sen 1)
	       djs (nth sen 0)]
	   (for [L (set (for [d djs :when (nil? (seq (:left d)))] (:right d)))]
	    (sb L ss nil)))))




(def types
     {:det [:right :det-noun]
      :adj [:all
	    [:any 
	     [:right :mod-noun]
	     [:left :cop-pred]]
	    [:opt [:left :mod-adj]]]
      :to [:all
	   
	   [:right :to-verb]]
      :adv [:any
	    [:right :mod-adj]
	    [:left :pred-comp]]
      :cop [:all 
	    [:left :subj-pred]
	    [:opt [:right :pred-comp]]
	    [:right :cop-pred]]
      :pronoun [:any
		; predicate
		[:left :cop-pred]
		;subject
		[:all
		 [:opt [:left :int-noun]]
		 [:right :subj-pred]]
		; do
		[:left :pred-do]
		; obj of prep
		[:left :prep-obj]
		]
      :noun [:any
	     ; no role
	     [:all 
	     ; [:opt [:any [:left :noun-comp] [:left :int-noun]]]
	      [:opt [:left :det-noun]]
	      [:0om [:left :mod-noun]]
	      [:0om [:right :noun-comp]]]
	     ; predicate
	     [:all
	      [:left :cop-pred]
	      [:opt [:left :det-noun]]
	      [:0om [:left :mod-noun]]
	      [:0om [:right :noun-comp]]]
	     ; subject
	     [:all 
	      [:opt [:any [:left :noun-comp] [:left :int-noun]]]
	      [:opt [:left :det-noun]]
	      [:0om [:left :mod-noun]]
	      [:0om [:right :noun-comp]]
	      [:right :subj-pred]]
	     ; do
	     [:all 
	      [:left :pred-do]
	      [:opt [:left :det-noun]]
	      [:0om [:left :mod-noun]]
	      [:0om [:right :noun-comp]]
	      ]
	     ; obj of prep
	     [:all 
	      [:left :prep-obj]
	      [:opt [:left :det-noun]]
	      [:0om [:left :mod-noun]]
	      [:0om [:right :noun-comp]]]
	     ]
      :verb [:all 
	     [:any 
	      [:left :subj-pred]
	      [:left :help-pred]]
	     
	     [:0om [:any 
		    [:right :pred-do]
		    [:right :pred-comp]]]
	     [:opt [:right :help-pred]]]
      :prep [:all
	     [:opt [:any 
		    [:left :noun-comp]
		    [:left :pred-comp]]]
	     [:right :prep-obj]]
      :int [:all
	    [:any [:left :pred-do]
	     [:left :noun-comp]]
	    [:any [:right :int-noun]
	     [:right :subj-pred]]]

      })

(defn types-to-disj [word l r]
  (lazy-seq
   (mapcat #(get-disjuncts l r (types %)) word)))

(def words {
"the"		#{:det}
"of"		#{:prep}
"and" 		#{:and}
"a"		#{:det}
"to"		#{:prep}
"in"		#{:prep}
"is"		#{:cop}
"you"		#{:pronoun}
"that"		#{:det :int}
"it"		#{:pronoun}
"he"		#{:pronoun}
"was"		#{:cop}
"for"		#{:prep}
"on"		#{:prep}
"are"		#{:cop}
"as"		#{:prep}
"with"		#{:prep}
"his"		#{:det :pronoun}
"they"		#{:pronoun}
"I" 		#{:pronoun}
"at"		#{:prep}
"be"		#{:verb}
"this"		#{:pronoun :det}
"have"		#{:verb}
"from"		#{:prep}
"or"		#{}
"one"		#{:adj :pronoun}
"had"		#{:verb}
"by"		#{:prep}
"word"		#{:noun}
"but"		#{}
"not"		#{:adv}
"what"		#{:int}
"all"		#{:noun}
"were"		#{:cop}
"we"		#{:pronoun}
"when"		#{:int}
"your"		#{:det}
"can"		#{}
"said" 		#{:verb}
"there"		#{:adv :pronoun}
"use"		#{:noun :verb}
"an"		#{:det}
"each"		#{:adj :pronoun}
"which"		#{:int}
"she"		#{:pronoun}
"do"		#{:verb :noun}
"how"		#{:int}
"their"		#{:det}
"if"		#{}
"will"		#{:noun :verb}
"up"		#{:pronoun :prep}
"other"		#{:adj}
"about"		#{:prep}

;not real
"house" #{:noun :verb}
"ate" #{:verb}
"cheese" #{:noun}
"dog" #{:noun}
"big" #{:adj}
"hard" #{:adj}
"old" #{:adj}
"capital" #{:noun :adj}})

(defn filter-while [pred coll]
  (for [x coll :while (pred x)]
    x))

(defn word-to-disj [word l r]
					;(filter #(nil? (seq (drop n (lazy-seq (concat (:left %) (:right %)))))))
  
  (if-let [t (words word)]
    (types-to-disj t l r)
    (types-to-disj (map first types) l r)))

(defn sen-to-disj [sen]
  (vec (map #(word-to-disj %1 %2 (- (count sen) %2 1)) sen (iterate inc 0))))

(defn parse-words [words]
  (set (map #(hash-map :sen words :graph (set %)) (process-djs (sen-to-disj words)))))

(defn prn-graph
  [{:keys [graph sen]}]
  (let [locs (reduce #(conj %1 (+ (last %1) (count %2) 1)) [0] sen)
	sb (new StringBuffer)]
    (loop [edges (reverse (sort-by #(- (:b %) (:a %)) graph))
	   cols (vec (replicate (locs (count sen)) " "))]
     (when (seq edges)
      (let [e (first edges)
	    left-space (locs (:a e))
	    line-length (- (locs (:b e))
			   (locs (:a e)))
	    right-space (- (locs (count sen)) left-space line-length)
	    cols (assoc cols left-space "|" (+ left-space line-length) "|")]
	(doseq [i (range (count cols))]
	    (cond 
	      (<= i left-space)
	      (.append sb (cols i))
	      (< i (+ left-space line-length))
	      (.append sb "-")
	      :else
	      (.append sb (cols i))))
	(.append sb (:type e))
	(.append sb "\n")
	(recur (rest edges) cols))))
 
    (.append sb (apply str (interpose \  sen)))
    (.append sb "\n")
    (.append sb "\n")
    (.toString sb)))

(defn print-all [solutions]
  (doseq [x solutions]
    (print (prn-graph x))))

(defn tpp [sen]
  (print-all (time (parse-words sen))))

(defn timeit [sen]
  (time (dorun (for [i (range 1000)] (parse-words sen)))))

(defn ssplit
  [str]
  (seq (.split str " ")))

(defn memoize*
  "Returns a memoized version of a referentially transparent function. The
  memoized version of the function keeps a cache of the mapping from arguments
  to results and, when calls with the same arguments are repeated often, has
  higher performance at the expense of higher memory use."
  [f]
  (let [mem (atom {})
	h (list :hits)
	m (list :misses)]
    (fn [& args]
      (if (#{h m} args)
	(@mem args 0)
	(if-let [e (find @mem args)]
	  (do
	    (swap! mem assoc h (inc (@mem h 0)))
	    (val e))
	  (let [ret (apply f args)]
	    (swap! mem assoc args ret m (inc (@mem m 0)))
	    ret))))))

(defn mem-ratio
  [f]
  (let [hits (f :hits)
	misses (f :misses)]
    (double (/ hits (+ hits misses)))))

(comment
  (do
    (def process-matches-when-match-left (memoize* process-matches-when-match-left))
    (def process-matches-when-match-right (memoize* process-matches-when-match-right)))
  )

(defn count-poss
  [sen]
  (apply * (map count (sen-to-disj sen))))
(defproject clj-lisp "0.1.0-SNAPSHOT"
  :description "Lisp implementation in Clojure"
  :url "https://github.com/r6eve/clj-lisp"
  :license {:name "Boost Software License - Version 1.0"
            :url "https://www.boost.org/users/license.html"}
  :dependencies [[org.clojure/clojure "1.10.1"]]
  :profiles {:dev {:global-vars {*warn-on-reflection* true
                                 *unchecked-math* :warn-on-boxed}}}
  :repl-options {:init-ns clj-lisp.core})

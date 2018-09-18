(defproject cascalog/cascalog-elephantdb "1.10.1-SNAPSHOT"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :source-paths ["src/clj"]
  :javac-options ["-source" "1.6" "-target" "1.6"]
  :jvm-opts ["-server" "-Xmx1024m"]
  :dependencies [[elephantdb/elephantdb-cascading "0.4.0-RC1"]]
  :plugins [[lein-midje "3.0-alpha4"]])

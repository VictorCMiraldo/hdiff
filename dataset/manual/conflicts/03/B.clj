(defproject cascalog/cascalog-elephantdb "1.10.1-SNAPSHOT"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :repositories {"conjars.org" "http://conjars.org/repo"}
  :source-paths ["src/clj"]
  :java-source-paths ["src/jvm"]
  :javac-options ["-source" "1.6" "-target" "1.6"]
  :jvm-opts ["-server" "-Xmx768m"]
  :dependencies [[elephantdb/elephantdb-cascading "0.3.5"]]
  :plugins [[lein-midje "3.0.0"]])

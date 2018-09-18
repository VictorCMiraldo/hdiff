(defn redis-stream
  "Returns a channel representing a stream from the Redis server located at :host. 'options'
   may also specify the :port and :charset used for this stream.

   Initially, the stream is not subscribed to any channels; to receive events, subscribe to
   channels using (subscribe stream & channel-names) or
   (pattern-subscribe stream & channel-patterns). To unsubscribe, use (unsubscribe ...) and
   (pattern-unsubscribe ...).

   Messages from the stream will be of the structure:

      {:channel \"channel-name\", :message \"message\"}

   :message will always be a string."
  ([options]
     (let [control-messages (channel)
	   stream (channel)

           options (merge
                     {:port 6379
                      :host "localhost"
                      :charset :utf-8
                      :name "redis-stream"}
                     options
                     {:on-connected
                      (fn [ch]
                        (siphon (fork control-messages) ch)
                        (siphon (filter-messages ch) stream))})

           connection (persistent-connection
                        #(tcp-client (merge options {:frame (redis-codec (:charset options))}))
                        options)

           _ (connection) ;; force a connection, since persistent-connection is lazy
           
           close-fn (fn []
                      (close-connection connection)
                      (close stream)
                      (close control-messages))] 

       (on-closed control-messages close-fn)
       (on-closed stream close-fn)
       
       (with-meta
         (splice stream control-messages)
         {:lamina.connections/close-fn close-fn
          :lamina.connections/reset-fn #(reset-connection connection)}))))

(defn redis-stream
  "Returns a channel representing a stream from the Redis server located at :host. 'options'
   may also specify the :port and :charset used for this stream.

   Initially, the stream is not subscribed to any channels; to receive events, subscribe to
   channels using (subscribe stream & channel-names) or
   (pattern-subscribe stream & channel-patterns). To unsubscribe, use (unsubscribe ...) and
   (pattern-unsubscribe ...).

   Messages from the stream will be of the structure {:channel \"channel-name\", :message \"message\"}.
   :message will always be a string."
  ([options]
     (let [options (merge {:port 6379 :charset :utf-8} options)
	   control-messages (channel)
	   stream (channel)
	   control-message-accumulator (atom [])]
       (receive-all control-messages
	 #(swap! control-message-accumulator conj %))
       (let [options (merge
		       {:name "redis"
			:description (str "redis stream @ " (:host options) ":" (:port options))}
		       options
		       {:connection-callback
			(fn [ch]
			  ;; NOTE: this is a bit of a race condition (subscription messages
			  ;; may be sent twice), but subscription messages are idempotent.
			  ;; Regardless, maybe clean this up.
			  (let [control-messages* (fork control-messages)]
			    (doseq [msg @control-message-accumulator]
			      (enqueue ch msg))
			    (siphon control-messages* ch))
			  (siphon (filter-messages ch) stream))})
	     connection (persistent-connection
			  #(tcp-client (merge options {:frame (redis-codec (:charset options))}))
			  options)
	     close-fn (fn []
			(close-connection connection)
			(close stream)
			(close control-messages))]
         (on-closed stream close-fn)
	 (on-closed control-messages close-fn)
	 (with-meta
	   (splice stream control-messages)
	   {:lamina.connections/close-fn close-fn})))))

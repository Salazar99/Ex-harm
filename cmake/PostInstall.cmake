#install third_party libraries
file(COPY ${S} DESTINATION ${IP}/ex-harm/lib FOLLOW_SYMLINK_CHAIN)
file(COPY ${B} DESTINATION ${IP}/ex-harm/lib FOLLOW_SYMLINK_CHAIN)
file(COPY ${A} DESTINATION ${IP}/ex-harm/lib FOLLOW_SYMLINK_CHAIN)
file(COPY ${Z} DESTINATION ${IP}/ex-harm/lib FOLLOW_SYMLINK_CHAIN)

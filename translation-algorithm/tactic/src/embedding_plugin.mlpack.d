src/embedding_plugin_MLPACK_DEPENDENCIES:=src/embedding src/g_embedding
src/embedding_plugin.cmo:$(addsuffix .cmo,$(src/embedding_plugin_MLPACK_DEPENDENCIES))
src/embedding_plugin.cmx:$(addsuffix .cmx,$(src/embedding_plugin_MLPACK_DEPENDENCIES))
src/embedding.cmx : FOR_PACK=-for-pack Embedding_plugin
src/g_embedding.cmx : FOR_PACK=-for-pack Embedding_plugin

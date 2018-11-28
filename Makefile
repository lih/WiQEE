WD := $(shell echo $$PWD)
PAGES_ROOT := src/pages
CSS_ROOT := src/css
TEMPLATE_ROOT := src/template
CACHE_ROOT := cache
STATIC_ROOT := static
PUBLIC_ROOT := public

SRC := $(wildcard $(PAGES_ROOT)/*.md)
STATIC_SRC := $(wildcard $(STATIC_ROOT)/*)
TARGETS := $(PUBLIC_ROOT)/style.css \
  $(SRC:$(PAGES_ROOT)/%.md=$(PUBLIC_ROOT)/%.html) \
  $(SRC:$(PAGES_ROOT)/%.md=$(PUBLIC_ROOT)/%.md) \
  $(STATIC_SRC:$(STATIC_ROOT)/%=$(PUBLIC_ROOT)/%) 

export PAGES_ROOT STATIC_ROOT CACHE_ROOT PUBLIC_ROOT

all: $(TARGETS)
	scripts/run-hook on-success

sync: all
	rsync -aP public/ wiqee:wiqee
watch:
	scripts/watch-make
clean:
	rm -rf $(TARGETS) $(CACHE_ROOT)

$(PUBLIC_ROOT): ; mkdir -p $@
$(CACHE_ROOT):  ; mkdir -p $@

.PRECIOUS: $(CACHE_ROOT)/%.mdc

ifdef LOCAL_HS_SOURCE
$(LOCAL_HS_SOURCE)/dist/build/WiQEE.js/WiQEE.js: $(LOCAL_HS_SOURCE)/exe/WiQEE.hs
	-haste-pkg unregister capricon
	cd $(LOCAL_HS_SOURCE) && rm -rf dist && haste-cabal install
$(STATIC_ROOT)/WiQEE.js: $(LOCAL_HS_SOURCE)/dist/build/WiQEE.js/WiQEE.js
	cp $< $@
endif

$(CACHE_ROOT)/%.mdc: $(PAGES_ROOT)/%.md | $(CACHE_ROOT)
	( cd $(PAGES_ROOT) >/dev/null && capricon prelude <<< "'$* source exec" ) > $@

$(CACHE_ROOT)/common.mdi: scripts/gencommon $(STATIC_ROOT)/noise.png $(STATIC_ROOT)/steps.png $(PAGES_ROOT)/prelude | $(CACHE_ROOT)
	$^ > $@

$(PUBLIC_ROOT)/%.html: $(CACHE_ROOT)/%.mdc $(TEMPLATE_ROOT)/header.html $(CACHE_ROOT)/common.mdi $(TEMPLATE_ROOT)/template.html | $(PUBLIC_ROOT)
	pandoc -s --mathml -V module:$* -H $(WD)/$(TEMPLATE_ROOT)/header.html --toc --template=$(WD)/$(TEMPLATE_ROOT)/template.html -f markdown -t html --css style.css $< $(CACHE_ROOT)/common.mdi > $@

$(PUBLIC_ROOT)/%.css: $(CSS_ROOT)/%.scss | $(PUBLIC_ROOT)
	sassc < $^ > $@

$(PUBLIC_ROOT)/%.png: $(STATIC_ROOT)/%.png | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.js: $(STATIC_ROOT)/%.js | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.jpg: $(STATIC_ROOT)/%.jpg | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.png: $(STATIC_ROOT)/%.png | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.tar.xz: $(STATIC_ROOT)/%.tar.xz | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.md: $(PAGES_ROOT)/%.md | $(PUBLIC_ROOT)
	cp $< $@

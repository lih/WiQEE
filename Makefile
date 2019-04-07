WD := $(shell echo $$PWD)
PAGES_ROOT := src/pages
CSS_ROOT := src/css
TEMPLATE_ROOT := src/template
CACHE_ROOT := cache
STATIC_ROOT := static
PUBLIC_ROOT := public
SASSC := $(shell which sassc || which scss 2>/dev/null)

SRC := $(wildcard $(PAGES_ROOT)/*.md)
STATIC_SRC := $(wildcard $(STATIC_ROOT)/*)
TARGETS := $(PUBLIC_ROOT)/style.css $(PUBLIC_ROOT)/test.css \
  $(SRC:$(PAGES_ROOT)/%.md=$(PUBLIC_ROOT)/%.html) \
  $(SRC:$(PAGES_ROOT)/%.md=$(PUBLIC_ROOT)/%.md) \
  $(STATIC_SRC:$(STATIC_ROOT)/%=$(PUBLIC_ROOT)/%) 
FULL_DATE := $(shell date +"%A, %B %d of %Y, at %R %p %Z")

export PAGES_ROOT STATIC_ROOT CACHE_ROOT PUBLIC_ROOT
.config.mk:
	echo "AUTOCOMMIT := " >> $@
	echo "export AUTOCOMMIT" >> $@
-include .config.mk

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
$(LOCAL_HS_SOURCE)/dist/build/capricon-engine.js/capricon-engine.js: $(LOCAL_HS_SOURCE)/exe/capricon-engine.hs
	-haste-pkg unregister capricon
	cd $(LOCAL_HS_SOURCE) && rm -rf dist && haste-cabal install
$(STATIC_ROOT)/capricon-engine.js: $(LOCAL_HS_SOURCE)/dist/build/capricon-engine.js/capricon-engine.js
	cp $< $@
endif

$(CACHE_ROOT)/env: | $(CACHE_ROOT)
	echo "'source-dir \"$(PAGES_ROOT)/\" def" > $@
	echo "'output-dir \"$(CACHE_ROOT)/\" def" >> $@
	echo "'cache-dir \"$(CACHE_ROOT)/\" def" >> $@

$(CACHE_ROOT)/%.mdc: $(PAGES_ROOT)/%.md $(CACHE_ROOT)/env | $(CACHE_ROOT)
	rm -f $(CACHE_ROOT)/$*.mdo.blob
	echo "'$* require" | capricon $(PAGES_ROOT)/prelude $(CACHE_ROOT)/env

$(CACHE_ROOT)/common.mdi: scripts/gencommon $(STATIC_ROOT)/noise.png $(STATIC_ROOT)/steps.png $(PAGES_ROOT)/prelude | $(CACHE_ROOT)
	$^ > $@

$(PUBLIC_ROOT)/%.html: $(CACHE_ROOT)/%.mdc $(TEMPLATE_ROOT)/header.html $(CACHE_ROOT)/common.mdi $(TEMPLATE_ROOT)/template.html | $(PUBLIC_ROOT)
	pandoc -s --mathjax='mathjax/MathJax.js?config=TeX-AMS_HTML' -V module:$* -V "full-date:$(FULL_DATE)" -H $(WD)/$(TEMPLATE_ROOT)/header.html --toc --template=$(WD)/$(TEMPLATE_ROOT)/template.html -f markdown+raw_html -t html --css style.css $< $(CACHE_ROOT)/common.mdi > $@

$(PUBLIC_ROOT)/theme-test.html: $(STATIC_ROOT)/theme-test.html
	cp $< $@

$(PUBLIC_ROOT)/%.css: $(CSS_ROOT)/%.scss $(wildcard $(CSS_ROOT)/_*.scss) | $(PUBLIC_ROOT)
	"$(SASSC)" -I$(CSS_ROOT) $< $@

$(PUBLIC_ROOT)/mathjax: $(STATIC_ROOT)/mathjax | $(PUBLIC_ROOT)
	cp -Ta $< $@

$(PUBLIC_ROOT)/%.png: $(STATIC_ROOT)/%.png | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.js: $(STATIC_ROOT)/%.js | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.woff2: $(STATIC_ROOT)/%.woff2 | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.jpg: $(STATIC_ROOT)/%.jpg | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.png: $(STATIC_ROOT)/%.png | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.tar.xz: $(STATIC_ROOT)/%.tar.xz | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.md: $(PAGES_ROOT)/%.md | $(PUBLIC_ROOT)
	cp $< $@

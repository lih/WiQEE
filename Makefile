WD := $(shell echo $$PWD)
PAGES_ROOT := src/pages
CSS_ROOT := src/css
TEMPLATE_ROOT := src/template
CACHE_ROOT := cache
STATIC_ROOT := static
PUBLIC_ROOT := public
SASSC := $(shell which sassc || which sass 2>/dev/null)

SRC := $(wildcard $(PAGES_ROOT)/*.md)
STATIC_SRC := $(wildcard $(STATIC_ROOT)/*)
TARGETS := $(PUBLIC_ROOT)/style.css $(PUBLIC_ROOT)/test.css \
  $(SRC:$(PAGES_ROOT)/%.md=$(PUBLIC_ROOT)/%.html) \
  $(SRC:$(PAGES_ROOT)/%.md=$(PUBLIC_ROOT)/%.pdf) \
  $(SRC:$(PAGES_ROOT)/%.md=$(PUBLIC_ROOT)/%.md) \
  $(STATIC_SRC:$(STATIC_ROOT)/%=$(PUBLIC_ROOT)/%) 
FULL_DATE := $(shell date +"%A, %B %d of %Y, at %R %p %Z")

PANDOC_MAJOR_VERSION := $(shell pandoc --version | head -1 | cut -d' ' -f2 | cut -d. -f1)

export PAGES_ROOT STATIC_ROOT CACHE_ROOT PUBLIC_ROOT
.config.mk:
	echo "CSS_COMPRESS :=" > $@
-include .config.mk

ifeq ($(CSS_COMPRESS),true)
SASSC_FLAGS += --style compressed
endif
ifeq ($(notdir $(SASSC)),sass)
SASSC_FLAGS += --no-source-map
endif

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

.PRECIOUS: $(CACHE_ROOT)/%.html.md $(CACHE_ROOT)/%.tex.md

ifdef LOCAL_HS_SOURCE
$(LOCAL_HS_SOURCE)/dist/build/capricon-engine.js/capricon-engine.js: $(LOCAL_HS_SOURCE)/exe/CaPriCon_Engine.hs
	-haste-pkg unregister capricon
	cd $(LOCAL_HS_SOURCE) && rm -rf dist && haste-cabal install
$(STATIC_ROOT)/capricon-engine.js: $(LOCAL_HS_SOURCE)/dist/build/capricon-engine.js/capricon-engine.js
	cp $< $@
endif

$(CACHE_ROOT)/env: | $(CACHE_ROOT)
	echo "'source-dir \"$(PAGES_ROOT)/\" def" > $@
	echo "'output-dir \"$(CACHE_ROOT)/\" def" >> $@
	echo "'cache-dir \"$(CACHE_ROOT)/\" def" >> $@

$(CACHE_ROOT)/%.tex.md $(CACHE_ROOT)/%.html.md: $(PAGES_ROOT)/%.md $(PAGES_ROOT)/prelude $(PAGES_ROOT)/render_prelude $(CACHE_ROOT)/env | $(CACHE_ROOT)
	rm -f $(CACHE_ROOT)/$*.mdo.blob
	echo "'$* require" | capricon $(PAGES_ROOT)/prelude $(PAGES_ROOT)/render_prelude $(CACHE_ROOT)/env

$(CACHE_ROOT)/common.html.mdi: scripts/gencommon $(STATIC_ROOT)/steps-32x32.png $(PAGES_ROOT)/prelude | $(CACHE_ROOT)
	$^ html > $@
$(CACHE_ROOT)/common.tex.mdi: scripts/gencommon $(STATIC_ROOT)/steps-32x32.png $(PAGES_ROOT)/prelude | $(CACHE_ROOT)
	$^ tex > $@

PANDOC_FLAGS := --standalone --toc -V "full-date:$(FULL_DATE)"
PANDOC_HTML_FLAGS := -t html --mathjax='mathjax/MathJax.js?config=TeX-AMS_HTML' --css style.css 
ifeq ($(PANDOC_MAJOR_VERSION),1)
PANDOC_FLAGS += -f markdown+definition_lists --smart
else
PANDOC_FLAGS += -f markdown+definition_lists+smart
endif

.PHONY: -%

$(PUBLIC_ROOT)/%.html: -H $(TEMPLATE_ROOT)/header.html --template $(TEMPLATE_ROOT)/template.html $(CACHE_ROOT)/%.html.md $(CACHE_ROOT)/common.html.mdi | $(PUBLIC_ROOT)
	pandoc $(PANDOC_FLAGS) $(PANDOC_HTML_FLAGS) -V module:$* $^ > $@
$(PUBLIC_ROOT)/%.pdf: $(CACHE_ROOT)/%.tex.md $(TEMPLATE_ROOT)/header.tex $(CACHE_ROOT)/common.tex.mdi | $(PUBLIC_ROOT)
	pandoc $(PANDOC_FLAGS) -H $(TEMPLATE_ROOT)/header.tex -V module:$* $< -o $@

$(PUBLIC_ROOT)/theme-test.html: $(STATIC_ROOT)/theme-test.html
	cp $< $@

$(PUBLIC_ROOT)/%.css: $(CSS_ROOT)/%.scss $(wildcard $(CSS_ROOT)/_*.scss) | $(PUBLIC_ROOT)
	"$(SASSC)" $(SASSC_FLAGS) -I$(CSS_ROOT) $< $@

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

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
clean:
	rm -rf $(TARGETS) $(CACHE_ROOT)

$(PUBLIC_ROOT): ; mkdir -p $@
$(CACHE_ROOT):  ; mkdir -p $@

.PRECIOUS: $(CACHE_ROOT)/%.mdc

$(CACHE_ROOT)/%.mdc: $(PAGES_ROOT)/%.md | $(CACHE_ROOT)
	( cd $(PAGES_ROOT) >/dev/null && capricon prelude <<< "'$* open exec" ) > $@

$(CACHE_ROOT)/common.mdi: scripts/gencommon | $(CACHE_ROOT)
	$< > $@

$(PUBLIC_ROOT)/%.html: $(CACHE_ROOT)/%.mdc $(TEMPLATE_ROOT)/header.html $(CACHE_ROOT)/common.mdi $(TEMPLATE_ROOT)/template.html | $(PUBLIC_ROOT)
	pandoc -s -V module:$* -H $(TEMPLATE_ROOT)/header.html --toc --template=$(PWD)/$(TEMPLATE_ROOT)/template.html -f markdown -t html --css style.css $< $(CACHE_ROOT)/common.mdi > $@

$(PUBLIC_ROOT)/%.css: $(CSS_ROOT)/%.scss | $(PUBLIC_ROOT)
	sassc < $^ > $@

$(PUBLIC_ROOT)/%.png: $(STATIC_ROOT)/%.png | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.jpg: $(STATIC_ROOT)/%.jpg | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.png: $(STATIC_ROOT)/%.png | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.tar.xz: $(STATIC_ROOT)/%.tar.xz | $(PUBLIC_ROOT)
	cp $< $@
$(PUBLIC_ROOT)/%.md: $(PAGES_ROOT)/%.md | $(PUBLIC_ROOT)
	cp $< $@

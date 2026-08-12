# frozen_string_literal: true

source "https://rubygems.org"

# Pinned exactly: `_layouts/post.html` is overridden with a copy taken from this
# version (for the `how_written` box). Keep both in sync when updating the theme.
gem "jekyll-theme-chirpy", "7.6.0"

gem "html-proofer", "~> 5.0", group: :test

platforms :windows, :jruby do
  gem "tzinfo", ">= 1", "< 3"
  gem "tzinfo-data"
end

gem "wdm", "~> 0.2.0", :platforms => [:windows]

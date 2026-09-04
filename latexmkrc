my $build_dir = ".latex-build/$$";

# Keep incomplete compiler output away from the tracked, reader-visible PDF.
$aux_dir = $build_dir;
$out_dir = $build_dir;
$out2_dir = '.';

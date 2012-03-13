/*
 * jQuery Infinite Drag
 * Version 0.2
 * Copyright (c) 2010 Ian Li (http://ianli.com)
 * Licensed under the MIT (http://www.opensource.org/licenses/mit-license.php) license.
 *
 * Requires:
 * jQuery	http://jquery.com
 *
 * Reference:
 * http://ianli.com/infinitedrag/ for Usage
 *
 * Versions:
 * 0.2 - Added move.
 * 0.1 - Initial implementation.
 */

(function($) {
	/**
	 * Function to create InfiniteDrag object.
	 */
	$.infinitedrag = function(draggable, draggable_options, tile_options) {
		return new InfiniteDrag(draggable, draggable_options, tile_options);
	};
	
	$.infinitedrag.VERSION = 0.2;
	
	/**
	 * The InfiniteDrag object.
	 */
	var InfiniteDrag = function(draggable, draggable_options, tile_options) {
		// Use self to reduce confusion about this.
		var self = this;

		var $draggable = $(draggable);
		var $viewport = $draggable.parent();
		$draggable.css({
			position: "relative",
			cursor: "move"
		});
		
		// Draggable options
		var _do = (draggable_options) ? draggable_options : {};

		// Tile options (DEFAULT)
		var _to = {
			class_name: "_tile",
			width: 100,
			height: 100,
			start_col: 0,
			start_row: 0,
			range_col: [-1000000, 1000000],
			range_row: [-1000000, 1000000],
			oncreate: function($element, i, j) {
				$element.text(i + "," + j);
			}
		};
		// Override tile options.
		for (var i in tile_options) {
			if (tile_options[i] !== undefined) {
				_to[i] = tile_options[i];
			}
		}
		
		// Override tile options based on draggable options.
		if (_do.axis == "x") {
			_to.range_row = [_to.start_row, _to.start_row];
		} else if (_do.axis == "y") {
			_to.range_col = [_to.start_col, _to.start_col];
		}
		
		// Creates the tile at (i, j).
		function create_tile(i, j) {
			if (i < _to.range_col[0] || _to.range_col[1] < i) {
				return;
			} else if (j < _to.range_row[0] || _to.range_row[1] < j) {
				return;
			}
			
			grid[i][j] = true;
			var x = i * _to.width;
			var y = j * _to.height;
			var $e = $draggable.append('<div></div>');

			var $new_tile = $e.children(":last");
			$new_tile.attr({
				"class": _to.class_name,
				col: i,
				row: j
			}).css({
				position: "absolute",
				left: x,
				top: y,
				width: _to.width,
				height: _to.height,
			});

			_to.oncreate($new_tile, i, j);
		};
		
		// Updates the containment box wherein the draggable can be dragged.
		var update_containment = function() {
			// Update viewport info.
			viewport_width = $viewport.width(),
			viewport_height = $viewport.height(),
			viewport_cols = Math.ceil(viewport_width / _to.width),
			viewport_rows = Math.ceil(viewport_height / _to.height);
			
			// Create containment box.
			var half_width = _to.width / 2,
				half_height = _to.height / 2,
				viewport_offset = $viewport.offset(),
				viewport_draggable_width = viewport_width - _to.width,
				viewport_draggable_height = viewport_height - _to.height;
			
			var containment = [
				(-_to.range_col[1] * _to.width) + viewport_offset.left + viewport_draggable_width,
				(-_to.range_row[1] * _to.height) + viewport_offset.top + viewport_draggable_height,
				(-_to.range_col[0] * _to.width) + viewport_offset.left,
				(-_to.range_row[0] * _to.height) + viewport_offset.top
			];
			
			$draggable.draggable("option", "containment", containment);
		};
		
		var update_tiles = function() {
			var $this = $draggable;
			var $parent = $this.parent();

			// Problem with .position() in Chrome/WebKit:
			// 		var pos = $(this).position();
			// So, we compute it ourselves.
			var pos = {
				left: $this.offset().left - $parent.offset().left,
				top: $this.offset().top - $parent.offset().top
			}

			var visible_left_col = Math.ceil(-pos.left / _to.width) - 1,
				visible_top_row = Math.ceil(-pos.top / _to.height) - 1;

			for (var i = visible_left_col; i <= visible_left_col + viewport_cols; i++) {
				for (var j = visible_top_row; j <= visible_top_row + viewport_rows; j++) {
					if (grid[i] === undefined) {
						grid[i] = {};
					} else if (grid[i][j] === undefined) {
						create_tile(i, j);
					}
				}
			}
		};
		
		
		// Public Methods
		//-----------------
		
		self.draggable = function() {
			return $draggable;
		};
		
		self.disabled = function(value) {
			if (value === undefined) {
				return $draggable;
			}
			
			$draggable.draggable("option", "disabled", value);
			
			$draggable.css({ cursor: (value) ? "default" : "move" });
		};
		
		self.move = function(col, row) {
			var offset = $draggable.offset();
			var move = {
				left: col * _to.width,
				top: row * _to.height
			};
			
			var new_offset = {
				left: offset.left - move.left,
				top: offset.top - move.top
			};
			
			if (_do.axis == "x") {
				new_offset.top = offset.top;
			} else if (_do.axis == "y") {
				new_offset.left = offset.left;
			}
			
			var containment = $draggable.draggable("option", "containment");
			
			if (containment[0] <= new_offset.left && new_offset.left <= containment[2]
				&& containment[1] <= new_offset.top && new_offset.top <= containment[3]) {
				$draggable.offset(new_offset);
				update_tiles();	
			} else {
				// Don't let the tile go beyond the right edge.
				if (new_offset.left < containment[0]) {
					new_offset.left = containment[0];
				}
				
				// Don't let the tile go beyond the left edge.
				if (new_offset.left > containment[2]) {
					new_offset.left = containment[2];
				}
				
				$draggable.offset(new_offset);
				update_tiles();
			}
		};
		
		self.center = function(col, row) {
			var x = _to.width * col,
				y = _to.height * row,
				half_width = _to.width / 2,
				half_height = _to.height / 2,
				half_vw_width = $viewport.width() / 2,
				half_vw_height = $viewport.height() / 2,
				offset = $draggable.offset();
				
			var new_offset = { 
				left: -x - (half_width - half_vw_width), 
				top: -y - (half_height - half_vw_height)
			};
			
			if (_do.axis == "x") {
				new_offset.top = offset.top;
			} else if (_do.axis == "y") {
				new_offset.left = offset.left;
			}
			
			$draggable.offset(new_offset);
			
			update_tiles();
		};

		// Setup
		//--------
		
		var viewport_width = $viewport.width(),
			viewport_height = $viewport.height(),
			viewport_cols = Math.ceil(viewport_width / _to.width),
			viewport_rows = Math.ceil(viewport_height / _to.height);

		$draggable.offset({
			left: $viewport.offset().left - (_to.start_col * _to.width),
			top: $viewport.offset().top - (_to.start_row * _to.height)
		});

		var grid = {};
		for (var i = _to.start_col, m = _to.start_col + viewport_cols; i < m && (_to.range_col[0] <= i && i <= _to.range_col[1]); i++) {
			grid[i] = {}
			for (var j = _to.start_row, n = _to.start_row + viewport_rows; j < n && (_to.range_row[0] <= j && j <= _to.range_row[1]); j++) {
				create_tile(i, j);
			}
		}
		
		// Handle resize of window.
		$(window).resize(function() {
			// HACK:
			// Update the containment when the window is resized
			// because the containment boundaries depend on the offset of the viewport.
			update_containment();
		});
		
		// The drag event handler.
		_do.drag = function(e, ui) {
			update_tiles();
		};
		
		$draggable.draggable(_do);
		
		update_containment();
	};
})(jQuery);

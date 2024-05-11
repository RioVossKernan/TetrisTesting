//MANUALLY SET THESE VALUES
const grid_width = 3;
const grid_height = 3;

//UPDATE SCREEN
function draw_screen(stg, inst_num){
    drawGrid(stg, inst_num)
    stg.render(svg, document)
}

function drawGrid(stg, inst_num) {
    //INITIALIZE GRID
    let tetrisGrid = new Grid({
        grid_location: {x: 50, y:50},
        cell_size: {x_size: 40, y_size: 40},
        grid_dimensions: {x_size: grid_width, y_size: grid_height}
    })

    //ADD VALUES TO GRID
    for (r = 0; r < grid_height; r++) {
        for (c = 0; c < grid_width; c++) {
            let tiles = instance.signature('Board').join(instance.field('tiles')).toString()
            if (tiles.includes(`${c}, ${r}`)){
                tetrisGrid.add({x: c, y: grid_height - r - 1}, new Rectangle({height: 40, width: 40, color: "green", borderColor: "black"}));
            }
        }
    }
    stg.add(tetrisGrid);
}

draw_screen(new Stage(), 0);
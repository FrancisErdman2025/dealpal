// content-script.js - DealPal persistent product extraction helper
(function() {
  // simple run-once extractor for product info on page
  function extract() {
    try {
      const title = document.querySelector('h1')?.innerText || document.title;

      // common price selectors across major e-commerce sites
      const priceEl = document.querySelector(
        '.price, [itemprop="price"], .priceblock_ourprice, .a-price .a-offscreen, .prod-Price, .price-characteristic'
      );

      const priceText = priceEl ? (priceEl.innerText || priceEl.textContent).trim() : null;
      const numericPrice = priceText ? parseFloat(priceText.replace(/[^\d\.]/g, '')) : null;

      const productInfo = {
        title: title || '',
        priceText: priceText || null,
        price: numericPrice,
        url: location.href,
        ts: Date.now()
      };

      // send info to background/popup if needed
      chrome.runtime.sendMessage({ type: 'PRODUCT_INFO', payload: productInfo });
    } catch (e) {
      console.error('DealPal content script extract error', e);
      chrome.runtime.sendMessage({ type: 'PRODUCT_INFO', payload: { title: document.title || '', url: location.href, ts: Date.now() } });
    }
  }

  // run once immediately
  extract();
})();
